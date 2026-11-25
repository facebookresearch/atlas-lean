/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.DenseToBinaryConverter
public import CSLibExt.Computability.Complexity.CookLevin.Hardness
public import CSLibExt.Computability.SatTimeM

/-!
# NP-hardness of `Cslib.CookLevin.satDec`

`satDec_npHard`: every `L ∈ MetaMathlibExt.ComplexityTheory.NP` polynomial-time many-one reduces to
`Cslib.CookLevin.satDec`, the binary-index SAT language. This is the hardness half of Cook-Levin
for `satDec`; `cook_levin_SAT_np_complete_of_isPolyTime` derives the full statement from
polynomial-time computability of the TimeM verifier `Cslib.CookLevin.satVerifier` (via
`Cslib.CookLevin.satDec_mem_NP_of_isPolyTime`), which `SatVerifier.Machine` supplies.

The reduction is the dense one (`Hardness.red`) followed by the dense-to-binary translation
(`DenseSAT.ToBinary.binConv`). Every clause of the Cook-Levin formula `Assembly.Phi` is a dense
clause over the same `V` variables (`Phi_length`), so the translation's renaming of variables is
consistent and preserves satisfiability (`ToBinary.cnfSat_binCNF_iff`).
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Hardness

open MetaMathlibExt ComplexityTheory Cslib.Complexity.DenseSAT Cslib.Complexity.CookLevin.Situation
  Cslib.Complexity.CookLevin.Assembly Cslib.Complexity.CookLevin.Precompute
  Cslib.Complexity.CookLevin.Package Turing

@[simp] theorem denseClause_length (V : ℕ) (ls : List (ℕ × Bool)) :
    (Family.denseClause V ls).length = V := by
  simp [Family.denseClause]

/-- **Every clause of the Cook–Levin formula has one slot per variable.** Let $E$ be an encoding
of a machine $M$, let $x$ and $Y$ be lists of input symbols of $M$, let $a$ be a symbol of its
output stack, and let $m, T \in \mathbb{N}$. Put $H = m + (T + 1)d + 1$, where $d$ is the window
depth of $M$. Then every clause of the Cook–Levin formula $\Phi(E, x, Y, a, m, T)$ is a dense
clause of length $(T + 1)(A + K H g)$, the number of variables of the layout of $E$ at time bound
$T$ and height $H$, where $A$, $K$ and $g$ are the label/state block size, the number of stacks
and the number of symbol codes of that layout. -/
theorem Phi_length {M : FinTM2} (E : Enc M) (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) :
    ∀ c ∈ Phi E x Ys acc m T, c.length = E.layout.numVars T (capH m T (depth M)) := by
  simp [Phi, Enc.accFamily, Enc.accCode, Enc.accCell, Shift.shFamily, Shift.shBlk,
    Family.family, Enc.initFamily, Enc.initCode, Enc.initOther, Enc.initIn, Enc.initCert,
    Enc.initPre, Enc.initTail]
  aesop

/-- **The dense-to-binary translation is polynomial-time in the canonical encoding.** The
translation of bit strings from the dense CNF encoding to the binary-index CNF encoding, as a
function on all bit strings, is polynomial-time computable with respect to the canonical
bitstring encoding of bit lists. -/
theorem isPolyTime_binConv : IsPolyTime ToBinary.binConv := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable ToBinary.computable
  have h2 := tm2ComputableInPolyTime_comp h EncodeBits.computable
  exact h2

/-- **Every NP problem reduces to binary-index CNF-SAT.** Every decision problem $L$ in NP has a
polynomial-time many-one reduction to the language of bit strings that encode a satisfiable CNF
formula in the binary-index encoding. -/
theorem satDec_npHard (L : DecisionProblem) (hL : L ∈ NP) :
    Cslib.CookLevin.PolyManyOneRed L Cslib.CookLevin.satDec := by
  obtain ⟨p, R, ⟨V₀⟩, hLR⟩ := hL
  let V : TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) (R ∘ id) :=
    TM2Composition.compComputable ToCanonical.computable V₀
  refine ⟨ToBinary.binConv ∘ red V p, (isPolyTime_red V p).comp isPolyTime_binConv, fun x => ?_⟩
  have h := v_correct V (R := fun a y => R (a, y) = true) (L' := fun a => L a = true)
    (fun _ => Iff.rfl) hLR x
  rw [Bool.eq_iff_iff]
  refine h.trans ?_
  change SAT (fR (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V)
    (ve V) x) ↔ _
  simp only [Function.comp_apply, red, fR, phiOf, ToBinary.binConv, ToBinary.conv_encodeCNF,
    ToBinary.satDec_encodeCNF]
  rw [ToBinary.cnfSat_binCNF_iff (Phi_length _ _ _ _ _ _), SAT, decodeCNF_encodeCNF]

/-- **Cook–Levin for binary-index CNF-SAT, given a polynomial-time verifier.** If the Boolean
result of the SAT verifier, as a function of pairs (formula code, assignment), is computable in
polynomial time, then the language of bit strings that encode a satisfiable CNF formula in the
binary-index encoding is in NP, and every decision problem in NP has a polynomial-time many-one
reduction to it. -/
theorem cook_levin_SAT_np_complete_of_isPolyTime
    (h : IsPolyTime fun xw => (Cslib.CookLevin.satVerifier xw).ret) :
    Cslib.CookLevin.satDec ∈ NP ∧
      ∀ L : DecisionProblem, L ∈ NP → Cslib.CookLevin.PolyManyOneRed L Cslib.CookLevin.satDec :=
  ⟨Cslib.CookLevin.satDec_mem_NP_of_isPolyTime h, satDec_npHard⟩

end Cslib.Complexity.CookLevin.Hardness
