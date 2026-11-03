/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Contraction formula on decomposable wedges (intertwining critical path)

Explicit alternating-sum formula for `CliffordAlgebra.contractLeft` applied
to decomposable wedges `ExteriorAlgebra.ιMulti R (n+1) v`, plus the
semilinear ext/transport lemma that pins a `→ₛₗ[σ]` map out of an exterior
power by its values on `ιMulti` generators.

* (§1) `exteriorPower_semilinear_ext` / `exteriorPower_semilinear_eq_zero`:
  the semilinear analogue of `exteriorPower.linearMap_ext` (which is
  linear-only), by span induction against `exteriorPower.ιMulti_span`.
  This is the transport shape the ring-change intertwining
  (`GrLiftIntertwining`) consumes.
* (§2) `contractLeft_ιMulti`: the alternating-sum formula, by iterating
  the antiderivation law `contractLeft_ι_mul` (peel `v 0`, recurse on the
  tail, reassemble with `Fin.sum_univ_succ`). Light-closure re-derivation
  of the `SelfDuality.lean` Leibniz rule (kept independent of that
  heavy file so the exactness route can import it cheaply).
* (§3) `koszulContract_ιMulti` / `koszulContract_exteriorPower_ιMulti`:
  the bundled `koszulContract` form that `contractExactAt` consumers use.

not attempted (blocked API, stays residual): Clifford-level naturality of
`contractLeft` under ring change / `ExteriorAlgebra.map` for semilinear
maps — absent from Mathlib, same gap as `GrLiftIntertwining` (missing-2).

Mathlib (all read-only):
* `LinearAlgebra/CliffordAlgebra/Contraction.lean`: `contractLeft_ι_mul`
  , `contractLeft_ι` , `contractLeft_one`.
* `LinearAlgebra/ExteriorAlgebra/Basic.lean`: `ιMulti_zero_apply` ,
  `ιMulti_succ_apply`.
* `LinearAlgebra/ExteriorPower/Basic.lean`: `ιMulti` ,
  `ιMulti_span`.
* `LinearAlgebra/Span/Defs.lean`: `Submodule.span_induction`.
* `Data/Fin/SuccPred.lean`: `succAbove_zero` ,
  `succAbove_ne_zero_zero`.

Project (read-only): `Regularity/Koszul/KoszulComplex.lean` (`koszulContract`
`koszulContract_apply`, `mem_ιMulti_piece`),
`Regularity/Koszul/AugmentedConeStep.lean` (`contractExactAt`, the consumption
shape), `Regularity/Koszul/SelfDuality.lean` (`contractLeft_ιMulti`,
prior art for §2).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ContractionFormula

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex

variable {R S : Type*} [CommRing R] [CommRing S]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N' : Type*} [AddCommGroup N'] [Module S N']

/-! ## §1. Semilinear ext on exterior powers -/

/-- Two semilinear maps out of an exterior power that agree on all
decomposable wedges are equal. Semilinear analogue of
`exteriorPower.linearMap_ext` (linear-only), by span induction against
`exteriorPower.ιMulti_span`.
-/
theorem exteriorPower_semilinear_ext (σ : R →+* S) {n : ℕ}
    {f g : ⋀[R]^n M →ₛₗ[σ] N'}
    (h : ∀ v : Fin n → M,
      f (exteriorPower.ιMulti R n v) = g (exteriorPower.ιMulti R n v)) :
    f = g := by
  ext x
  have hspan := exteriorPower.ιMulti_span R n M
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact h v
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul r y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- A semilinear map out of an exterior power that vanishes on all
decomposable wedges is zero.
-/
theorem exteriorPower_semilinear_eq_zero (σ : R →+* S) {n : ℕ}
    {f : ⋀[R]^n M →ₛₗ[σ] N'}
    (h : ∀ v : Fin n → M, f (exteriorPower.ιMulti R n v) = 0) :
    f = 0 := by
  apply exteriorPower_semilinear_ext σ
  intro v
  rw [h v, LinearMap.zero_apply]

/-! ## §2. The alternating-sum formula -/

/-- Tails commute with skipping a successor: deleting position `j'.succ`
then taking the tail is taking the tail then deleting position `j'`.
By cases on `i < j'`, via the `succAbove` unfolding lemmas.
(Combinatorial helper, same proof as `SelfDuality.vecTail_comp_succAbove_succ`.)
-/
theorem vecTail_comp_succAbove_succ (M : Type*) [AddCommGroup M]
    {N : ℕ} (v : Fin (N + 1 + 1) → M) (j' : Fin (N + 1)) :
    Matrix.vecTail (v ∘ Fin.succAbove (j'.succ)) =
      (Matrix.vecTail v) ∘ Fin.succAbove j' := by
  funext i
  change v (Fin.succAbove (j'.succ) (i.succ)) = v ((Fin.succAbove j' i).succ)
  congr 1
  by_cases h : Fin.castSucc i < j'
  · have hiv : i.val < j'.val := h
    have hL : Fin.castSucc (i.succ) < j'.succ := by
      change (Fin.castSucc (i.succ)).val < (j'.succ).val
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hL,
      Fin.succAbove_of_castSucc_lt _ _ h, Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_succ]
  · have hle : j' ≤ Fin.castSucc i := le_of_not_gt h
    have hiv : j'.val ≤ i.val := hle
    have hL : j'.succ ≤ Fin.castSucc (i.succ) := by
      change (j'.succ).val ≤ (Fin.castSucc (i.succ)).val
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hL,
      Fin.succAbove_of_le_castSucc _ _ hle]

/-- Leibniz rule for `contractLeft` on decomposable wedges: contracting
`ιMulti v` sums over deleting each factor, with alternating signs from
the peel position. HilbertFunctionCount on `n`, peeling `v 0` via
`contractLeft_ι_mul`; the `j = 0` term has no sign, deeper terms pick up
one minus per peel.
-/
theorem contractLeft_ιMulti (φ : M →ₗ[R] R) (n : ℕ) (v : Fin n.succ → M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
        (ExteriorAlgebra.ιMulti R n.succ v) =
      ∑ j : Fin n.succ, ((-1 : R)^(j.val) * φ (v j)) •
        ExteriorAlgebra.ιMulti R n (v ∘ Fin.succAbove j) := by
  induction n with
  | zero =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul,
      ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one,
      mul_zero, sub_zero, Fin.sum_univ_one]
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ n ih =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul, ih (Matrix.vecTail v),
      Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    conv_rhs => rw [Fin.sum_univ_succ]
    have htail : Matrix.vecTail v = v ∘ Fin.succAbove 0 := by
      rw [Fin.succAbove_zero]
      rfl
    have hT0 : φ (v 0) • ExteriorAlgebra.ιMulti R (n.succ) (Matrix.vecTail v) =
        (((-1 : R)^((0 : Fin (n.succ).succ).val) * φ (v 0)) •
          ExteriorAlgebra.ιMulti R (n.succ) (v ∘ Fin.succAbove 0)) := by
      rw [htail]
      simp
    rw [hT0]
    congr 1
    apply Finset.sum_congr rfl
    intro j' _
    have hA : Fin.succAbove (j'.succ) 0 = 0 :=
      Fin.succAbove_ne_zero_zero (by simp)
    have hB := vecTail_comp_succAbove_succ M v j'
    have hX := ExteriorAlgebra.ιMulti_succ_apply (R := R)
      (v ∘ Fin.succAbove (j'.succ))
    rw [Function.comp_apply, hA, hB] at hX
    rw [hX, Algebra.mul_smul_comm, ← neg_smul]
    congr 1
    have hval : (j'.succ).val = j'.val + 1 := Fin.val_succ j'
    have hφ : φ ((Matrix.vecTail v) j') = φ (v (j'.succ)) := rfl
    rw [hval, hφ, pow_succ]
    ring

/-! ## §3. Bundled `koszulContract` form -/

/-- Coe pushes through sums of exterior-power elements. -/
theorem exteriorPower_subtype_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → ↥(⋀[R]^n M)) :
    ((∑ i ∈ s, f i : ↥(⋀[R]^n M)) : ExteriorAlgebra R M) =
      ∑ i ∈ s, ((f i : ↥(⋀[R]^n M)) : ExteriorAlgebra R M) :=
  map_sum (Submodule.subtype _) _ _

/-- Coe pushes through scalar multiples of exterior-power elements. -/
@[simp]
theorem exteriorPower_subtype_smul {n : ℕ} (c : R) (x : ↥(⋀[R]^n M)) :
    ((c • x : ↥(⋀[R]^n M)) : ExteriorAlgebra R M) =
      c • ((x : ↥(⋀[R]^n M)) : ExteriorAlgebra R M) :=
  map_smul (Submodule.subtype _) _ _

/-- The bundled contraction on a decomposable wedge: `koszulContract`
deletes each factor in turn with alternating signs. This is the form
`contractExactAt` consumers use (cycles/boundaries of `koszulContract`).
-/
theorem koszulContract_ιMulti (φ : M →ₗ[R] R) (n : ℕ) (v : Fin n.succ → M) :
    koszulContract φ n ⟨ExteriorAlgebra.ιMulti R n.succ v,
      mem_ιMulti_piece _ _⟩ =
      ∑ j : Fin n.succ, ((-1 : R)^(j.val) * φ (v j)) •
        (⟨ExteriorAlgebra.ιMulti R n (v ∘ Fin.succAbove j),
          mem_ιMulti_piece _ _⟩ : ↥(⋀[R]^n M)) := by
  apply Subtype.ext
  rw [koszulContract_apply, contractLeft_ιMulti, exteriorPower_subtype_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [exteriorPower_subtype_smul]

/-- The bundled contraction on `exteriorPower.ιMulti` generators
(`rfl`-equal to the `ExteriorAlgebra.ιMulti` form above).
-/
theorem koszulContract_exteriorPower_ιMulti (φ : M →ₗ[R] R) (n : ℕ)
    (v : Fin n.succ → M) :
    koszulContract φ n (exteriorPower.ιMulti R n.succ v) =
      ∑ j : Fin n.succ, ((-1 : R)^(j.val) * φ (v j)) •
        (⟨ExteriorAlgebra.ιMulti R n (v ∘ Fin.succAbove j),
          mem_ιMulti_piece _ _⟩ : ↥(⋀[R]^n M)) :=
  koszulContract_ιMulti φ n v

end ContractionFormula
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
