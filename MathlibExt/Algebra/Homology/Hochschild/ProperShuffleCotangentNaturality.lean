/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentQuasiIsoDegreeZero
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianPositiveKernel
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormAlgebraNaturality
public import MathlibExt.LinearAlgebra.TensorPower.PermutationActionNaturality

/-!
# Naturality of the proper-shuffle cotangent augmentation

Over a rational ground ring, the first Eulerian projector
identifies the proper relation kernel. Compatible algebra
and coefficient maps therefore induce shifted quotient
chain maps commuting with the cotangent augmentation.
The carrier universes are independent; neither coefficient
nor algebra flatness is required for these maps.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v v' v'' w w' w''

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle

open ModuleCat.Algebra.Hochschild
open ModuleCat.Algebra.Hochschild.Symmetric

section IndependentWorlds

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {C : Type v''} [CommRing C] [Algebra k C]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]
  {N : Type w'} [AddCommGroup N] [Module k N] [Module B N]
  [SMulCommClass k B N] [IsScalarTower k B N]
  {P : Type w''} [AddCommGroup P] [Module k P] [Module C P]
  [SMulCommClass k C P] [IsScalarTower k C P]

omit [Module A M] [SMulCommClass k A M] [IsScalarTower k A M]
  [Module B N] [SMulCommClass k B N] [IsScalarTower k B N] in
/-- The original coefficient tensor map intertwines the zero-plus-first
projectors across independent ring and coefficient universes. -/
theorem firstOperator_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    (linearMap g.toNonUnitalAlgHom f n).comp (firstEulerianOperator k A M n) =
      (firstEulerianOperator k B N n).comp (linearMap g.toNonUnitalAlgHom f n) := by
  have h (i : ℕ) : (linearMap g.toNonUnitalAlgHom f n).comp (coefficientEulerianOperator k A M n i) =
      (coefficientEulerianOperator k B N n i).comp (linearMap g.toNonUnitalAlgHom f n) :=
    TensorPower.coefficientRationalPermutationAction_naturality n
      (Equiv.Perm.eulerianElement n i) g.toLinearMap f
  simp only [firstEulerianOperator, LinearMap.comp_add, LinearMap.add_comp, h]

/-- Actual first-projector naturality preserves the proper-shuffle
relation modules. No relation-preservation certificate is supplied. -/
theorem relations_map (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    rawPositiveRelations k A M n ≤
      (rawPositiveRelations k B N n).comap (linearMap g.toNonUnitalAlgHom f n) := by
  intro x hx
  rw [rawPositiveRelations_eq_firstEulerianKernel] at hx
  rw [rawPositiveRelations_eq_firstEulerianKernel]
  change firstEulerianOperator k B N n (linearMap g.toNonUnitalAlgHom f n x) = 0
  have hx' : firstEulerianOperator k A M n x = 0 := hx
  have h := LinearMap.congr_fun (firstOperator_naturality k g f n) x
  change linearMap g.toNonUnitalAlgHom f n (firstEulerianOperator k A M n x) =
    firstEulerianOperator k B N n (linearMap g.toNonUnitalAlgHom f n x) at h
  exact h.symm.trans ((congrArg (linearMap g.toNonUnitalAlgHom f n) hx').trans
    (linearMap g.toNonUnitalAlgHom f n).map_zero)

/-- The quotient map on the original proper-shuffle tensor levels. -/
def quotientLinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n) →ₗ[k]
      ((N ⊗[k] TensorPower k n B) ⧸ rawPositiveRelations k B N n) :=
  (rawPositiveRelations k A M n).mapQ (rawPositiveRelations k B N n)
    (linearMap g.toNonUnitalAlgHom f n) (relations_map k g f n)

/-- Every original representative is mapped by the original coefficient-first
Hochschild tensor map before taking its original quotient class. -/
theorem quotientLinearMap_mkQ (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ)
    (x : M ⊗[k] TensorPower k n A) :
    quotientLinearMap k g f n ((rawPositiveRelations k A M n).mkQ x) =
      (rawPositiveRelations k B N n).mkQ (linearMap g.toNonUnitalAlgHom f n x) := rfl

/-- The original coefficient and algebra identity maps induce the quotient identity. -/
theorem quotientLinearMap_id (n : ℕ) :
    quotientLinearMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n = LinearMap.id := by
  refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n => ?_)
  refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k n A => ?_)
  change quotientLinearMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n
      ((rawPositiveRelations k A M n).mkQ x) = (rawPositiveRelations k A M n).mkQ x
  have h := LinearMap.congr_fun (linearMap_id (k := k) (A := A) (M := M) n) x
  exact (quotientLinearMap_mkQ k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n x).trans
    (congrArg (rawPositiveRelations k A M n).mkQ h)

/-- Native composition of the parameter maps is retained by the same quotient maps. -/
theorem quotientLinearMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P) (n : ℕ) :
    (quotientLinearMap k h f' n).comp (quotientLinearMap k g f n) =
      quotientLinearMap k (h.comp g) (f'.comp f) n := by
  refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n => ?_)
  refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k n A => ?_)
  change quotientLinearMap k h f' n
      (quotientLinearMap k g f n ((rawPositiveRelations k A M n).mkQ x)) =
    quotientLinearMap k (h.comp g) (f'.comp f) n ((rawPositiveRelations k A M n).mkQ x)
  have h₁ := quotientLinearMap_mkQ k g f n x
  have h₂ := quotientLinearMap_mkQ k h f' n (linearMap g.toNonUnitalAlgHom f n x)
  have h₃ := quotientLinearMap_mkQ k (h.comp g) (f'.comp f) n x
  have hc := LinearMap.congr_fun (linearMap_comp g.toNonUnitalAlgHom h.toNonUnitalAlgHom f f' n) x
  exact (congrArg (quotientLinearMap k h f' n) h₁).trans
    (h₂.trans ((congrArg (rawPositiveRelations k C P n).mkQ hc).trans h₃.symm))

omit [Algebra ℚ k] in
/-- The original ground-linear boundary value is the stored A-linear boundary value. -/
theorem originalBoundary_value (n : ℕ) (x : M ⊗[k] TensorPower k (n + 1) A) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    (ModuleCat.Algebra.Hochschild.boundary k A M n).hom x = algebraBoundary k A M n x := by
  let _ := opModule A M
  let _ := actionsComm A M
  let _ := kOpComm k A M
  let _ := kOpTower k A M
  have h := congrArg ModuleCat.Hom.hom (ModuleCat.Algebra.Hochschild.chainComplex_d k A M n)
  exact (LinearMap.congr_fun h x).symm

omit [Algebra ℚ k] in
/-- Actual algebra-action compatibility earns the entire original boundary square,
with independent original coefficient and ring universes. -/
theorem originalBoundary_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (x : M ⊗[k] TensorPower k (n + 1) A) :
    algebraBoundary k B N n (linearMap g.toNonUnitalAlgHom f (n + 1) x) =
      linearMap g.toNonUnitalAlgHom f n (algebraBoundary k A M n x) := by
  let _ := opModule A M
  let _ := actionsComm A M
  let _ := kOpComm k A M
  let _ := kOpTower k A M
  let _ := opModule B N
  let _ := actionsComm B N
  let _ := kOpComm k B N
  let _ := kOpTower k B N
  have h := LinearMap.congr_fun (linearMap_boundary_comm g.toNonUnitalAlgHom f hf
    (by intro a m; exact hf a m) n) x
  change (ModuleCat.Algebra.Hochschild.boundary k B N n).hom (linearMap g.toNonUnitalAlgHom f (n + 1) x) =
    linearMap g.toNonUnitalAlgHom f n ((ModuleCat.Algebra.Hochschild.boundary k A M n).hom x) at h
  exact ((originalBoundary_value k n (linearMap g.toNonUnitalAlgHom f (n + 1) x)).symm.trans h).trans
    (congrArg (linearMap g.toNonUnitalAlgHom f n) (originalBoundary_value k n x))

end IndependentWorlds

section Complexes

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  {A B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- The quotient-level maps assemble into a native chain map by the complete boundary square. -/
def chainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    positiveQuotient k A M ⟶ positiveQuotient k B N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (quotientLinearMap k g f n)) (by
    intro n
    let β₁ := quotientLinearMap k g f (n + 1)
    let β₀ := quotientLinearMap k g f n
    let d₁ : ((N ⊗[k] TensorPower k (n + 1) B) ⧸ rawPositiveRelations k B N (n + 1)) →ₗ[k]
        ((N ⊗[k] TensorPower k n B) ⧸ rawPositiveRelations k B N n) :=
      ((positiveQuotient k B N).d (n + 1) n).hom
    let d₀ : ((M ⊗[k] TensorPower k (n + 1) A) ⧸ rawPositiveRelations k A M (n + 1)) →ₗ[k]
        ((M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n) :=
      ((positiveQuotient k A M).d (n + 1) n).hom
    apply ModuleCat.hom_ext
    change d₁.comp β₁ = β₀.comp d₀
    refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k (n + 1) A) ⧸ rawPositiveRelations k A M (n + 1) => ?_)
    refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k (n + 1) A => ?_)
    have h₁ := quotientLinearMap_mkQ k g f (n + 1) x
    have hd₁ := positiveQuotient_d_mk k B N n (linearMap g.toNonUnitalAlgHom f (n + 1) x)
    have hd₀ := positiveQuotient_d_mk k A M n x
    have h₀ := quotientLinearMap_mkQ k g f n (algebraBoundary k A M n x)
    have hb := originalBoundary_naturality k g f hf n x
    exact (congrArg d₁ h₁).trans (hd₁.trans
      ((congrArg (rawPositiveRelations k B N n).mkQ hb).trans
        (h₀.symm.trans (congrArg β₀ hd₀.symm)))))

/-- The original quotient component is retained by the native chain-map constructor. -/
theorem chainMap_f (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    ((chainMap k g f hf).f n).hom = quotientLinearMap k g f n := rfl

/-- The quotient map commutes with the original coefficient tensor map and projection. -/
@[reassoc]
theorem chainMap_projection (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    properShuffleProjection k A M ≫ chainMap k g f hf =
      originalAlgebraCoefficientChainMap k g f hf ≫ properShuffleProjection k B N := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, chainMap_f,
    originalAlgebraCoefficientChainMap_f]
  change (quotientLinearMap k g f n).comp (rawPositiveRelations k A M n).mkQ =
    (rawPositiveRelations k B N n).mkQ.comp (linearMap g.toNonUnitalAlgHom f n)
  refine LinearMap.ext (fun x : M ⊗[k] TensorPower k n A => ?_)
  exact quotientLinearMap_mkQ k g f n x

/-- The original identity parameter maps give the quotient identity. -/
theorem chainMap_id :
    chainMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) (by intro a m; rfl) =
      𝟙 (positiveQuotient k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change quotientLinearMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n = LinearMap.id
  exact quotientLinearMap_id k n

/-- Composition of original compatible algebra and coefficient maps gives
composition of the quotient maps, including all original degrees. -/
@[reassoc]
theorem chainMap_comp {C : Type v} [CommRing C] [Algebra k C]
    {P : Type w} [AddCommGroup P] [Module k P] [Module C P]
    [SMulCommClass k C P] [IsScalarTower k C P]
    (g : A →ₐ[k] B) (h : B →ₐ[k] C) (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hf : ∀ a m, f (a • m) = g a • f m) (hf' : ∀ b n, f' (b • n) = h b • f' n) :
    chainMap k g f hf ≫ chainMap k h f' hf' =
      chainMap k (h.comp g) (f'.comp f) (by
        intro a m
        change f' (f (a • m)) = h (g a) • f' (f m)
        rw [hf, hf']) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (quotientLinearMap k h f' n).comp (quotientLinearMap k g f n) =
    quotientLinearMap k (h.comp g) (f'.comp f) n
  exact quotientLinearMap_comp k g h f f' n

/-- The native positive-index restriction retains the original n+1 degree shift. -/
def cotangentChainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    properCotangentComplex k A M ⟶ properCotangentComplex k B N :=
  HomologicalComplex.restrictionMap (chainMap k g f hf) ComplexShape.positiveNatEmbedding

/-- Every shifted component is the original quotient degree n+1 map. -/
theorem cotangentChainMap_f (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    ((cotangentChainMap k g f hf).f n).hom = quotientLinearMap k g f (n + 1) := rfl

/-- The original coefficient cotangent map uses the one-form algebra map and the degree-one
coordinates. -/
def cotangentModuleMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientCotangentModule k A M ⟶ coefficientCotangentModule k B N :=
  (cotangentFormOneIso k A M).inv ≫ (coefficientFormAlgebraComplexMap k g f hf).f 1 ≫
    (cotangentFormOneIso k B N).hom

/-- The original one-form quotient descent commutes with the algebra and coefficient maps. -/
@[reassoc]
theorem degreeMap_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    (chainMap k g f hf).f 1 ≫ properCotangentDegreeMap k B N =
      properCotangentDegreeMap k A M ≫
        (coefficientFormAlgebraComplexMap k g f hf).f 1 := by
  apply ModuleCat.hom_ext
  let D₁ := (properCotangentDegreeMap k B N).hom
  let D₀ := (properCotangentDegreeMap k A M).hom
  let F₁ := ((coefficientFormAlgebraComplexMap k g f hf).f 1).hom
  change D₁.comp (quotientLinearMap k g f 1) = F₁.comp D₀
  refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k 1 A) ⧸ rawPositiveRelations k A M 1 => ?_)
  refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k 1 A => ?_)
  have hq := quotientLinearMap_mkQ k g f 1 x
  have h := congrArg
    (fun t : chainComplex k A M ⟶ coefficientDifferentialFormComplex k B N => (t.f 1).hom)
    (coefficientDifferentialFormChainMap_algebra k g f hf)
  let T₁ := ((coefficientDifferentialFormChainMap k B N).f 1).hom
  have hΓ := LinearMap.congr_fun (originalAlgebraCoefficientChainMap_f k g f hf 1) x
  have hv : T₁ (linearMap g.toNonUnitalAlgHom f 1 x) =
      F₁ (((coefficientDifferentialFormChainMap k A M).f 1).hom x) :=
    (congrArg T₁ hΓ.symm).trans (LinearMap.congr_fun h x)
  exact (congrArg D₁ hq).trans hv

/-- The same original scalar cotangent augmentation commutes with these parameter maps. -/
@[reassoc]
theorem scalarAugmentation_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    (chainMap k g f hf).f 1 ≫ properCotangentScalarAugmentation k B N =
      properCotangentScalarAugmentation k A M ≫ cotangentModuleMap k g f hf := by
  change (chainMap k g f hf).f 1 ≫ (properCotangentDegreeMap k B N ≫ (cotangentFormOneIso k B N).hom) =
    (properCotangentDegreeMap k A M ≫ (cotangentFormOneIso k A M).hom) ≫
      ((cotangentFormOneIso k A M).inv ≫ (coefficientFormAlgebraComplexMap k g f hf).f 1 ≫
        (cotangentFormOneIso k B N).hom)
  calc
    _ = ((chainMap k g f hf).f 1 ≫ properCotangentDegreeMap k B N) ≫ (cotangentFormOneIso k B N).hom :=
      (Category.assoc _ _ _).symm
    _ = (properCotangentDegreeMap k A M ≫ (coefficientFormAlgebraComplexMap k g f hf).f 1) ≫
        (cotangentFormOneIso k B N).hom :=
      congrArg (fun t => t ≫ (cotangentFormOneIso k B N).hom) (degreeMap_naturality k g f hf)
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The full shifted proper-shuffle cotangent chain augmentation is natural.
The input is the original module-action compatibility, not a desired chain square. -/
@[reassoc]
theorem augmentation_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    cotangentChainMap k g f hf ≫ properShuffleCotangentMap k B N =
      properShuffleCotangentMap k A M ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentModuleMap k g f hf) := by
  apply (ChainComplex.toSingle₀Equiv (properCotangentComplex k A M) (coefficientCotangentModule k B N)).injective
  apply Subtype.ext
  change ((cotangentChainMap k g f hf ≫ properShuffleCotangentMap k B N).f 0) =
    ((properShuffleCotangentMap k A M ≫
      (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentModuleMap k g f hf)).f 0)
  simp only [HomologicalComplex.comp_f, properShuffleCotangentMap_f_zero, ChainComplex.single₀_map_f_zero]
  exact scalarAugmentation_naturality k g f hf

end Complexes

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle
