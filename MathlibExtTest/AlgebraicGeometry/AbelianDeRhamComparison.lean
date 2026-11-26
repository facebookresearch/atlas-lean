/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

/-!
# Tests for the Galois action on the de Rham period ring of `ℂ_p`

`p` is not a unit of `𝓞_ℂ_p`, by instance; the action on `𝓞_ℂ_p` is the completed action on `ℂ_p`
and preserves the norm; the action on `W(𝓞_ℂ_p^♭)[1/p]` fixes `ℚ_p`; the filtration starts at
`Fil^0 = B_dR^+` and decreases; and the action on `B_dR^+` extends the action on
`W(𝓞_ℂ_p^♭)[1/p]`.
-/

open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

variable (p : ℕ) [Fact p.Prime]

/-- `p` is not a unit of `𝓞_ℂ_p`; instance search finds this. -/
example : ¬IsUnit (p : 𝓞_ℂ_[p]) := Fact.out

/-- The elements of `𝓞_ℂ_p` are those of norm at most one: `p` is one of them, `p⁻¹` is not. -/
example : (p : PadicComplex p) ∈ 𝓞_ℂ_[p] := (p : 𝓞_ℂ_[p]).2

example : (p : PadicComplex p)⁻¹ ∉ 𝓞_ℂ_[p] := by
  rw [mem_padicComplexInt_iff, norm_inv, ← map_natCast (algebraMap ℚ_[p] (PadicComplex p)),
    norm_algebraMap', Padic.norm_p, inv_inv, not_le]
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- The action on `𝓞_ℂ_p` is the completed action on `ℂ_p`, and it preserves the norm. -/
example (σ : Galois p) (x : 𝓞_ℂ_[p]) :
    ((integralGalois p σ x : 𝓞_ℂ_[p]) : PadicComplex p) = completionGalois p σ x := rfl

example (σ : Galois p) (x : PadicComplex p) : ‖completionGalois p σ x‖ = ‖x‖ :=
  norm_completionGalois p σ x

/-- The action on `W(𝓞_ℂ_p^♭)[1/p]` fixes `ℚ_p`. -/
example (σ : Galois p) (c : ℚ_[p]) :
    preDeRhamGalois p σ (padicToPreDeRham p c) = padicToPreDeRham p c := by
  rw [← RingHom.comp_apply, preDeRhamGalois_comp_padicToPreDeRham]

section Completion

variable [IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]]

/-- `Fil^0 B_dR^+ = B_dR^+`. -/
example : fil p 0 = ⊤ := by
  have : Subsingleton (PreDeRham p ⧸ thetaKer p ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
  exact eq_top_iff.2 fun x _ => (RingHom.mem_ker).2 (Subsingleton.elim _ _)

/-- The filtration decreases: `Fil^{j + 1} B_dR^+ ⊆ Fil^j B_dR^+`. -/
example (j : ℕ) : fil p (j + 1) ≤ fil p j := fun x hx => by
  rw [fil, RingHom.mem_ker] at hx ⊢
  change AdicCompletion.evalₐ (thetaKer p) j x = 0
  rw [← AdicCompletion.factorPow_evalₐ (thetaKer p) j.le_succ x]
  change Ideal.Quotient.factorPow _ j.le_succ (evalBdR p (j + 1) x) = 0
  rw [hx, map_zero]

/-- The action on `B_dR^+` extends the action on `W(𝓞_ℂ_p^♭)[1/p]` and fixes `ℚ_p`. -/
example (σ : Galois p) (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ))
    (x : PreDeRham p) :
    bdRPlusGaloisLinear p σ h (ofPreDeRham p x) = ofPreDeRham p (preDeRhamGalois p σ x) :=
  bdRPlusGalois_ofPreDeRham p σ h x

example (σ : Galois p) (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) (c : ℚ_[p]) :
    bdRPlusGaloisLinear p σ h (algebraMap ℚ_[p] (BdRPlus p) c) =
      algebraMap ℚ_[p] (BdRPlus p) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  congr 1
  exact map_one (bdRPlusGalois p σ h)

end Completion
