/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_ProjSpace.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the definitions and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import MathlibExt.AlgebraicGeometry.ProjSpace
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Charts of projective space over a ring and finite products of projective spaces

Projective `n`-space over a commutative ring `R` is `Proj` of
`MvPolynomial (Fin (n + 1)) R` with its standard grading; its proper structure
morphism `ProjSpace.π R n` to `Spec R` is defined in
`MathlibExt.AlgebraicGeometry.ProjSpace`. This file records the standard affine
charts `D₊(X i)` and their generating ratios `X k / X i`, and the fibre product
`prodOver R e` over `Spec R` of finitely many projective spaces.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section StdCover

open MvPolynomial AlgebraicGeometry.Proj

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal
      ≤ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial _ R)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi f hf
  have hf' : f.IsHomogeneous i := (MvPolynomial.mem_homogeneousSubmodule i f).mp hf
  change f ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R
  rw [← pow_one (MvPolynomial.idealOfVars _ R), MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  rw [MvPolynomial.mem_support_iff] at hx
  have hdeg : Finsupp.degree x = i := by
    rw [Finsupp.degree_eq_weight_one]; exact hf' hx
  omega

end StdCover

section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem X_mem_one (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)

/-- The `R`-algebra structure on the standard chart `D₊(X i)`. -/
scoped instance algebraAway (i : Fin (n + 1)) :
    Algebra R (Away 𝒜 (MvPolynomial.X i)) :=
  ((HomogeneousLocalization.fromZeroRingHom 𝒜 _).comp
    (grad0Equiv R n).toRingHom).toAlgebra

theorem awayι_comp_π (i : Fin (n + 1)) :
    Proj.awayι 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
      ≫ π R n
      = Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X i)))) := by
  unfold π
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The section `X k / X i` of the standard chart `D₊(X i)`. -/
def ratio (i k : Fin (n + 1)) : Away 𝒜 (MvPolynomial.X i) :=
  Away.mk 𝒜 (X_mem_one R n i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_one R n k)

theorem ratio_self (i : Fin (n + 1)) :
    ratio R n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio, Away.val_mk, HomogeneousLocalization.val_one,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem val_algebraMap (i : Fin (n + 1)) (r : R) :
    (algebraMap R (Away 𝒜 (MvPolynomial.X i)) r).val
      = algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.C r) := by
  rfl

end Setup

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard affine open cover of projective space by the charts
`D₊(X i)`. -/
abbrev affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 (fun j => MvPolynomial.X j)
    (fun j => X_mem_one R n j) (fun _ => one_pos)
    (irrelevant_le_span_X R n)

theorem affineOpenCover_f (j : Fin (n + 1)) :
    (affineOpenCover R n).openCover.f j
      = Proj.awayι 𝒜 (MvPolynomial.X j) (X_mem_one R n j) one_pos := rfl

end StdCover

section AdjoinRatio

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem awayMk_monomial (i : Fin (n + 1)) (d : ℕ)
    (e : Fin (n + 1) →₀ ℕ) (hd : e.degree = d) (r : R)
    (hm : MvPolynomial.monomial e r ∈ 𝒜 (d • 1)) :
    Away.mk 𝒜 (X_mem_one R n i) d (MvPolynomial.monomial e r) hm
      = algebraMap R _ r * ∏ j, (ratio R n i j) ^ (e j) := by
  have hdsum : ∑ j, e j = d := by
    rw [← hd, Finsupp.degree]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => Finsupp.notMem_support_iff.mp hj)).symm
  apply HomogeneousLocalization.val_injective
  have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
      = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
  rw [hval, map_mul, map_prod]
  simp only [map_pow, ratio, ← hval, Away.val_mk,
    val_algebraMap, Localization.mk_pow,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_prod, Localization.mk_mul]
  congr 1
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
  · refine Subtype.ext ?_
    push_cast
    simp only [Finset.prod_pow_eq_pow_sum, pow_one, one_mul, hdsum]

theorem adjoin_range_ratio (i : Fin (n + 1)) :
    Algebra.adjoin R (Set.range (ratio R n i)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem_one R n i) z
  have ha' : a.IsHomogeneous d := (mem_homogeneousSubmodule d a).mp (by simpa using ha)
  have hdeg : ∀ e ∈ a.support, (e : Fin (n + 1) →₀ ℕ).degree = d := fun e he => by
    rw [Finsupp.degree_eq_weight_one]; exact ha' (MvPolynomial.mem_support_iff.mp he)
  have hsum : Away.mk 𝒜 (X_mem_one R n i) d a ha
      = ∑ e ∈ a.support.attach,
          Away.mk 𝒜 (X_mem_one R n i) d
            (MvPolynomial.monomial e.1 (a.coeff e.1))
            ((mem_homogeneousSubmodule _ _).mpr
              (isHomogeneous_monomial _
                (by simp only [smul_eq_mul, mul_one]; exact hdeg e.1 e.2))) := by
    apply HomogeneousLocalization.val_injective
    have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
        = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
    rw [hval, map_sum]
    simp only [← hval, Away.val_mk]
    rw [Finset.sum_attach a.support
      (fun e => Localization.mk (monomial e (a.coeff e))
        (⟨(X i)^d, ⟨d, rfl⟩⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (n+1)) R))),
      ← Localization.mk_sum]
    congr 1
    exact MvPolynomial.as_sum a
  rw [hsum]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [awayMk_monomial R n i d e.1 (hdeg e.1 e.2) (a.coeff e.1)]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun j _ =>
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _)

end AdjoinRatio

section ProdOver

variable (R : Type u) [CommRing R]

/-- Auxiliary recursion building the fibre product over `Spec R` of the
projective spaces of dimensions `e k`, together with its map to `Spec R`. -/
def prodOverAux :
    ∀ {m : ℕ}, (Fin m → ℕ) → Σ (P : Scheme.{u}), P ⟶ Spec (.of R)
  | 0, _ => ⟨Spec (.of R), 𝟙 _⟩
  | m + 1, e =>
    let prev := @prodOverAux m (e ∘ Fin.succ)
    ⟨pullback (π R (e 0)) prev.2,
     pullback.fst _ _ ≫ π R (e 0)⟩

/-- The fibre product over `Spec R` of the projective spaces of dimensions
`e 0, …, e (m - 1)`. -/
abbrev prodOver {m : ℕ} (e : Fin m → ℕ) : Scheme.{u} :=
  (prodOverAux R e).1

/-- The structure morphism of `prodOver R e` to `Spec R`. -/
abbrev prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    prodOver R e ⟶ Spec (.of R) :=
  (prodOverAux R e).2

theorem isProper_prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    IsProper (prodOverπ R e) := by
  induction m with
  | zero => exact inferInstanceAs (IsProper (𝟙 _))
  | succ m ih =>
    have := ih (e ∘ Fin.succ)
    change IsProper (pullback.fst _ _ ≫ π R (e 0))
    infer_instance

/-- A finite fibre product of projective spaces is proper over the base. -/
instance instIsProperProdOverπ {m : ℕ} (e : Fin m → ℕ) : IsProper (prodOverπ R e) :=
  isProper_prodOverπ R e

end ProdOver

end ProjSpace

end AlgebraicGeometry
