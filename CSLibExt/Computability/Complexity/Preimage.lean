/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.MapFirst
public import CSLibExt.Computability.CookLevin
import CSLibExt.Computability.Complexity.SatVerifierTM

/-!
# Polynomial preimages of canonical NP languages

The verifier for a preimage computes the reduction on its first input and
preserves the certificate. Every conversion uses the canonical encodings.
The first-component machine and the output-length bound come from
`CSLibExt.Computability.Complexity.MapFirst`.
-/

@[expose] public section

namespace MetaMathlibExt.ComplexityTheory

open Cslib.Complexity Cslib.Complexity.Preimage
open Cslib.CookLevin Cslib.Logic.PL

private theorem satVerifier_sound {x w : List Bool}
    (h : (satVerifier (x, w)).ret = true) : satDec x = true := by
  cases hd : decodeCNF x with
  | none => simp [satVerifier_none hd] at h
  | some φ =>
    rw [satVerifier_some hd, checkCNF_ret] at h
    have hs : CNFSat φ := cnfSat_iff_exists_satisfies.2 ⟨_, h⟩
    rw [(decodeCNF_eq_some_iff x φ).1 hd]
    exact (DenseSAT.ToBinary.satDec_encodeCNF φ).2 hs

/-- Pulling SAT back along a polynomial map preserves NP membership.
SAT verifier soundness holds even for certificates above its length bound. -/
theorem satDec_comp_mem_NP {f : List Bool → List Bool}
    (hf : IsPolyTime f) : satDec ∘ f ∈ NP := by
  obtain ⟨q, hq⟩ := hf.length_bound
  refine ⟨q, fun p => (satVerifier (f p.1, p.2)).ret,
    hf.map_fst.comp SatVerifier.Machine.isPolyTime_satVerifier, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨w, hw, ha⟩ := (satVerifier_verifies (f x)).1 hx
    rw [Polynomial.eval_X] at hw
    exact ⟨w, hw.trans (hq x), ha⟩
  · rintro ⟨w, -, ha⟩
    exact satVerifier_sound ha

/-- Canonical NP is closed under polynomial-time preimages.
Cook–Levin supplies a verifier sound for arbitrarily long certificates,
so enlarging the transformed witness bound introduces no false positives. -/
theorem comp_mem_NP {L : DecisionProblem} {f : List Bool → List Bool}
    (hL : L ∈ NP) (hf : IsPolyTime f) : L ∘ f ∈ NP := by
  obtain ⟨g, hg, he⟩ :=
    SatVerifier.Machine.cook_levin_SAT_np_complete.2 L hL
  have hEq : L ∘ f = satDec ∘ (g ∘ f) := funext fun x => he (f x)
  rw [hEq]
  exact satDec_comp_mem_NP (hf.comp hg)

/-- NP membership transfers backwards along a polynomial many-one reduction. -/
theorem mem_NP_of_polyManyOneRed {L K : DecisionProblem}
    (hK : K ∈ NP) (hr : PolyManyOneRed L K) : L ∈ NP := by
  obtain ⟨f, hf, he⟩ := hr
  have hEq : L = K ∘ f := funext he
  rw [hEq]
  exact comp_mem_NP hK hf

/-- Canonical coNP is closed under polynomial-time preimages. -/
theorem comp_mem_coNP {L : DecisionProblem} {f : List Bool → List Bool}
    (hL : L ∈ coNP) (hf : IsPolyTime f) : L ∘ f ∈ coNP :=
  comp_mem_NP (L := Lᶜ) (f := f) hL hf

end MetaMathlibExt.ComplexityTheory

namespace Cslib.CookLevin

/-- The same reduction function reduces the complements. -/
theorem PolyManyOneRed.compl
    {L K : MetaMathlibExt.ComplexityTheory.DecisionProblem}
    (h : PolyManyOneRed L K) : PolyManyOneRed Lᶜ Kᶜ := by
  obtain ⟨f, hf, he⟩ := h
  exact ⟨f, hf, fun x => congrArg Bool.not (he x)⟩

end Cslib.CookLevin
