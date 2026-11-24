/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplexRegularSequence
public import MathlibExt.LinearAlgebra.ExteriorPower.FinsuppFiniteSupport
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Koszul complexes on arbitrary finitely supported free coordinates

The differential and quotient augmentation are the existing native Koszul
constructions. Actual finite-coordinate retractions reduce every positive
cycle to a finite family. Projectivity uses the actual free exterior terms.
No Lie algebra, PBW model, finite ambient index or characteristic premise is used.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace KoszulComplex

variable (R : Type u) [CommRing R] {I : Type v}

/-- The coefficient functional on the original arbitrary free module. -/
def finsuppFunctional (a : I → R) : (I →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R a

/-- The original finite-coordinate inclusion preserves the actual coefficient
functional; this is equality of the original linear maps. -/
theorem finsuppFunctional_comp_finsetInclude (a : I → R) (s : Finset I) :
    (finsuppFunctional R a).comp (Finsupp.finsetInclude R s) =
      familyFunctional R (fun i : s => a i.val) := by
  classical
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, finsuppFunctional, Finsupp.finsetInclude_apply,
    map_sum, Finsupp.linearCombination_single, familyFunctional,
    Fintype.linearCombination_apply]

/-- Actual boundary construction for an arbitrary family whose finite
distinct subfamilies are weakly regular. The exactness input is the proved
finite-family theorem, not a supplied boundary or resolution. -/
theorem finsupp_exact_cycles_of_finite_isWeaklyRegular
    (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j)))
    (k : ℕ) (z : ⋀[R]^(k + 1) (I →₀ R))
    (hz : differential R (I →₀ R) (finsuppFunctional R a) k z = 0) :
    ∃ w : ⋀[R]^(k + 2) (I →₀ R),
      differential R (I →₀ R) (finsuppFunctional R a) (k + 1) w = z := by
  classical
  obtain ⟨s, zS, hzS⟩ := exteriorPower.exists_preimage_finset R (k + 1) z
  let aS : s → R := fun i => a i.val
  let inc := Finsupp.finsetInclude R s
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hregular : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => aS (e j)) :=
    ha (fun j => (e j).val) (Subtype.val_injective.comp e.injective)
  have hfunc : (finsuppFunctional R a).comp inc = familyFunctional R aS :=
    finsuppFunctional_comp_finsetInclude R a s
  have hcycle : differential R (s → R) (familyFunctional R aS) k zS = 0 := by
    apply exteriorPower.map_finsetInclude_injective R s k
    rw [map_zero]
    calc
      exteriorPower.map k inc
          (differential R (s → R) (familyFunctional R aS) k zS) =
          differential R (I →₀ R) (finsuppFunctional R a) k
            (exteriorPower.map (k + 1) inc zS) :=
        (LinearMap.congr_fun (differential_naturality R (s → R)
          (familyFunctional R aS) (finsuppFunctional R a) inc hfunc k) zS).symm
      _ = 0 := by rw [hzS, hz]
  obtain ⟨wS, hwS⟩ := family_exact_cycles_of_isWeaklyRegular R aS e hregular k zS hcycle
  refine ⟨exteriorPower.map (k + 2) inc wS, ?_⟩
  calc
    _ = exteriorPower.map (k + 1) inc
        (differential R (s → R) (familyFunctional R aS) (k + 1) wS) :=
      LinearMap.congr_fun (differential_naturality R (s → R)
        (familyFunctional R aS) (finsuppFunctional R a) inc hfunc (k + 1)) wS
    _ = z := by rw [hwS, hzS]

/-- The actual arbitrary-family Koszul complex on the free finitely
supported coordinate module, using the original Koszul boundary. -/
abbrev finsuppComplex (a : I → R) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  complex R (I →₀ R) (finsuppFunctional R a)

@[simp]
theorem finsuppFunctional_single (a : I → R) (i : I) :
    finsuppFunctional R a (Finsupp.single i 1) = a i := by
  classical
  rw [finsuppFunctional, Finsupp.linearCombination_single, one_smul]

/-- Signed deletion on original standard free-coordinate wedges. -/
theorem finsuppDifferential_apply_basis (a : I → R) (n : ℕ) (f : Fin (n + 1) → I) :
    differential R (I →₀ R) (finsuppFunctional R a) n
      (exteriorPower.ιMulti R (n + 1) (fun j => Finsupp.single (f j) 1)) =
    ∑ j : Fin (n + 1), (((-1 : R) ^ j.val) * a (f j)) •
      exteriorPower.ιMulti R n (fun q => Finsupp.single (f (j.succAbove q)) 1) := by
  rw [differential_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finsuppFunctional_single, smul_smul]
  rfl

/-- The actual differential on scalar multiples of coordinate wedges. -/
theorem finsuppDifferential_smul_basis (a : I → R) (n : ℕ) (p : R)
    (f : Fin (n + 1) → I) :
    differential R (I →₀ R) (finsuppFunctional R a) n
      (p • exteriorPower.ιMulti R (n + 1) (fun j => Finsupp.single (f j) 1)) =
    ∑ j : Fin (n + 1), (-1 : R) ^ j.val •
      ((p * a (f j)) • exteriorPower.ιMulti R n
        (fun q => Finsupp.single (f (j.succAbove q)) 1)) := by
  rw [map_smul, finsuppDifferential_apply_basis, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_smul]
  congr 1
  exact mul_left_comm p ((-1 : R) ^ j.val) (a (f j))

/-- The original functional range ideal is generated by the actual family. -/
theorem finsuppIdeal_eq_span (a : I → R) :
    ideal R (I →₀ R) (finsuppFunctional R a) = Ideal.span (Set.range a) := by
  change LinearMap.range (Finsupp.linearCombination R a) = _
  rw [Finsupp.range_linearCombination, Ideal.submodule_span_eq]

/-- Every original arbitrary-coordinate term is free. No finite index is needed. -/
theorem finsuppComplex_free (a : I → R) (n : ℕ) :
    Module.Free R ((finsuppComplex R a).X n) := by
  change Module.Free R (⋀[R]^n (I →₀ R))
  infer_instance

/-- Every original arbitrary-coordinate term is a native projective object. -/
theorem finsuppComplex_projective (a : I → R) (n : ℕ) :
    CategoryTheory.Projective ((finsuppComplex R a).X n) := by
  classical
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  change CategoryTheory.Projective (ModuleCat.of R (⋀[R]^n (I →₀ R)))
  exact ModuleCat.projective_of_free ((Finsupp.basisSingleOne (R := R)).exteriorPower n)

/-- The original quotient augmentation remains exactly the native Koszul augmentation. -/
abbrev finsuppAugmentation (a : I → R) := augmentation R (I →₀ R) (finsuppFunctional R a)

/-- Its zero-degree exactness is the existing original quotient-augmentation proof. -/
theorem finsuppAugmentation_exact_zero (a : I → R) :
    (augmentationShortComplex R (I →₀ R) (finsuppFunctional R a)).Exact :=
  augmentation_exact_zero R (I →₀ R) (finsuppFunctional R a)

/-- Genuine finite weak regularity yields positive exactness of the original
arbitrary-coordinate complex; the boundary is constructed by finite support. -/
theorem finsuppComplex_exactAt_of_finite_isWeaklyRegular (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j))) (k : ℕ) :
    (finsuppComplex R a).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := finsuppComplex R a) (j := k + 1) (i := k + 2) (k := k)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k by rfl)),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro z hz
  change ((complex R (I →₀ R) (finsuppFunctional R a)).d (k + 1) k) z = 0 at hz
  rw [complex_d_succ] at hz
  change differential R (I →₀ R) (finsuppFunctional R a) k z = 0 at hz
  change ∃ w : ⋀[R]^(k + 2) (I →₀ R),
    ((complex R (I →₀ R) (finsuppFunctional R a)).d (k + 2) (k + 1)) w = z
  rw [complex_d_succ]
  exact finsupp_exact_cycles_of_finite_isWeaklyRegular R a ha k z hz

/-- The original quotient augmentation is a quasi-isomorphism when actual
finite distinct subfamilies are weakly regular. No exactness datum is an input. -/
theorem finsuppAugmentation_quasiIso_of_finite_isWeaklyRegular (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j))) :
    QuasiIso (augmentation R (I →₀ R) (finsuppFunctional R a)) := by
  refine ⟨fun j => ?_⟩
  cases j with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso
          (S₂ := augmentationShortComplex R (I →₀ R) (finsuppFunctional R a)) ?_).mpr
          ⟨augmentation_exact_zero R (I →₀ R) (finsuppFunctional R a),
            (ModuleCat.epi_iff_surjective _).mpr
              (augmentationLinearLifted_surjective R (I →₀ R) (finsuppFunctional R a))⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · simp only [Iso.refl_hom]
          exact complex_d_succ R (I →₀ R) (finsuppFunctional R a) 0
        · simp only [Iso.refl_hom]
          exact augmentation_f_zero R (I →₀ R) (finsuppFunctional R a)
      all_goals rfl
  | succ j =>
      rw [quasiIsoAt_iff_exactAt']
      · exact finsuppComplex_exactAt_of_finite_isWeaklyRegular R a ha j
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- Actual arbitrary-coordinate native projective resolution from genuine
finite weak regularity. Concrete polynomial/diagonal clients earn this premise. -/
def finsuppProjectiveResolutionOfFiniteIsWeaklyRegular (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j))) :
    ProjectiveResolution (ModuleCat.of R (ULift.{max u v, u}
      (R ⧸ ideal R (I →₀ R) (finsuppFunctional R a)))) where
  complex := finsuppComplex R a
  projective := finsuppComplex_projective R a
  π := augmentation R (I →₀ R) (finsuppFunctional R a)
  quasiIso := finsuppAugmentation_quasiIso_of_finite_isWeaklyRegular R a ha

end KoszulComplex
