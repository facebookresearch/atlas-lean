/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexRegularSequence
public import MathlibExt.Algebra.Homology.KoszulComplexHomologyZero
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Projective resolutions from weakly regular Koszul complexes

For a finite weakly regular family, the quotient augmentation is a
quasi-isomorphism. Degree zero follows from the augmentation cokernel, and
positive degrees follow from the Koszul boundary construction. Since all
terms are projective, the Koszul complex gives a projective resolution of
the quotient and computes its derived tensor products.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace KoszulComplex

universe u v

variable (R : Type u) [CommRing R]

section GenericFamily

variable {I : Type v} [Fintype I]

/-- The augmentation of the Koszul complex of a finite weakly regular family
is a quasi-isomorphism, including in degree zero. -/
theorem augmentation_quasiIso_of_isWeaklyRegular
    {n : ℕ} (a : I → R) (e : Fin n ≃ I)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun i => a (e i))) :
    QuasiIso (augmentation R (I → R) (familyFunctional R a)) := by
  refine ⟨fun j => ?_⟩
  cases j with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso
          (S₂ := augmentationShortComplex R (I → R) (familyFunctional R a)) ?_).mpr
          ⟨augmentation_exact_zero R (I → R) (familyFunctional R a),
            (ModuleCat.epi_iff_surjective _).mpr
              (augmentationLinearLifted_surjective R (I → R) (familyFunctional R a))⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · simp only [Iso.refl_hom]
          exact complex_d_succ R (I → R) (familyFunctional R a) 0
        · simp only [Iso.refl_hom]
          exact augmentation_f_zero R (I → R) (familyFunctional R a)
      all_goals rfl
  | succ j =>
      rw [quasiIsoAt_iff_exactAt']
      · exact familyComplex_exactAt_of_isWeaklyRegular R a e ha j
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The Koszul complex of a finite weakly regular family gives a projective
resolution of the universe-lifted quotient by the generated ideal. -/
def familyProjectiveResolutionOfIsWeaklyRegular
    {n : ℕ} (a : I → R) (e : Fin n ≃ I)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun i => a (e i))) :
    ProjectiveResolution
      (ModuleCat.of R (ULift.{max u v, u}
        (R ⧸ ideal R (I → R) (familyFunctional R a)))) where
  complex := familyComplex R a
  projective := familyComplex_projective R a
  π := augmentation R (I → R) (familyFunctional R a)
  quasiIso := augmentation_quasiIso_of_isWeaklyRegular R a e ha

/-- The actual complex in the constructed resolution is the original
finite-family Koszul complex. -/
theorem familyProjectiveResolution_complex
    {n : ℕ} (a : I → R) (e : Fin n ≃ I)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun i => a (e i))) :
    (familyProjectiveResolutionOfIsWeaklyRegular R a e ha).complex =
      familyComplex R a := rfl

end GenericFamily

/-- For a weakly regular family indexed by `Fin n`, the degree-`q` homology
of its Koszul complex tensored on the left with `N` computes `Tor` of `N`
with the universe-lifted quotient by the generated ideal. -/
def regularFiniteFamilyTensorHomologyIsoTor
    {n : ℕ} (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (N : ModuleCat.{u} R) (q : ℕ) :
    ((((tensoringLeft (ModuleCat.{u} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a)).homology q ≅
        (((Tor (ModuleCat.{u} R) q).obj N).obj
          (ModuleCat.of R (ULift.{u, u}
            (R ⧸ ideal R (Fin n → R) (familyFunctional R a))))) :=
  ((familyProjectiveResolutionOfIsWeaklyRegular R a (Equiv.refl _) ha).isoLeftDerivedObj
    ((tensoringLeft (ModuleCat.{u} R)).obj N) q).symm

/-- The native finite-rank Koszul resolution with the original quotient
itself as target. The canonical module equivalence removes the existing
augmentation lift; no quotient or homology model is changed. -/
def finiteFamilyProjectiveResolutionQuotient
    {n : ℕ} (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a)) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ ideal R (Fin n → R) (familyFunctional R a))) := by
  let P := familyProjectiveResolutionOfIsWeaklyRegular R a (Equiv.refl _) ha
  let Q := R ⧸ ideal R (Fin n → R) (familyFunctional R a)
  let e : ModuleCat.of R (ULift.{u, u} Q) ≅ ModuleCat.of R Q :=
    (ULift.moduleEquiv : ULift.{u, u} Q ≃ₗ[R] Q).toModuleIso
  exact
    { complex := P.complex
      projective := P.projective
      π := P.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map e.hom }

/-- For a weakly regular family indexed by `Fin n`, the degree-`q` homology
of its Koszul complex tensored on the left with `N` computes `Tor` of `N`
with the quotient by the generated ideal, without a universe lift. -/
def regularFiniteFamilyTensorHomologyIsoTorQuotient
    {n : ℕ} (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (N : ModuleCat.{u} R) (q : ℕ) :
    ((((tensoringLeft (ModuleCat.{u} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a)).homology q ≅
        (((Tor (ModuleCat.{u} R) q).obj N).obj
          (ModuleCat.of R (R ⧸ ideal R (Fin n → R) (familyFunctional R a)))) :=
  ((finiteFamilyProjectiveResolutionQuotient R a ha).isoLeftDerivedObj
    ((tensoringLeft (ModuleCat.{u} R)).obj N) q).symm

end KoszulComplex
