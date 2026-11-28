/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.GroupTheory.PermutationBilinearCocycle
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Subgroup.Center

@[expose] public section

universe uA uB uι uA' uB' uA'' uB''

namespace PermutationBilinearCocycle

section TupleActionDef

variable (A : Type uA) (ι : Type uι) [Group A]

/-- Permutation of tuple coordinates as a multiplicative automorphism action. -/
def tupleActionHom : Equiv.Perm ι →* MulAut (ι → A) where
  toFun σ := permuteEquiv (A := A) σ
  map_one' := by
    ext u i
    simp
  map_mul' σ τ := by
    ext u i
    simp

end TupleActionDef

@[simp]
theorem tupleActionHom_apply (A : Type uA) (ι : Type uι) [Group A]
    (σ : Equiv.Perm ι) (u : ι → A) :
    (tupleActionHom A ι σ) u = permute σ u :=
  rfl

@[simp]
theorem tupleActionHom_one (A : Type uA) (ι : Type uι) [Group A] :
    tupleActionHom A ι (1 : Equiv.Perm ι) = 1 := by
  ext u i
  simp

theorem tupleActionHom_mul (A : Type uA) (ι : Type uι) [Group A]
    (σ τ : Equiv.Perm ι) :
    tupleActionHom A ι (σ * τ) =
      tupleActionHom A ι σ * tupleActionHom A ι τ := by
  ext u i
  simp

section MonomialBaseDef

variable (A : Type uA) (ι : Type uι) [Group A]

/-- The semidirect product of coefficient tuples and coordinate permutations. -/
abbrev MonomialBase : Type _ :=
  SemidirectProduct (ι → A) (Equiv.Perm ι) (tupleActionHom A ι)

end MonomialBaseDef

section MonomialLiftAuxDef

variable (A : Type uA) (B : Type uB) (ι : Type uι)
  [Group A] [AddCommGroup B] [Fintype ι] [LinearOrder ι]
variable (b : SkewBicharacter A B)

/-- The auxiliary semidirect-product lift of the bilinear tuple extension. -/
abbrev MonomialLiftAux : Type _ :=
  SemidirectProduct (Extension b ι) (Equiv.Perm ι) (permActionHom (ι := ι) b)

end MonomialLiftAuxDef

/-- The monomial lift with the specified bilinear coefficient extension. -/
abbrev MonomialLift {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    (b : SkewBicharacter A B) (ι : Type uι) [Fintype ι] [LinearOrder ι] : Type _ :=
  MonomialLiftAux A B ι b

section ProjCompat

variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
  (b : SkewBicharacter A B) (ι : Type uι) [Fintype ι] [LinearOrder ι]

theorem proj_compat (σ : Equiv.Perm ι) :
    (NormalizedCocycleExtension.projHom (lowerNormalizedCocycle (ι := ι) b)).comp
        ((permActionHom (ι := ι) b σ).toMonoidHom) =
      (tupleActionHom A ι σ).toMonoidHom.comp
        (NormalizedCocycleExtension.projHom (lowerNormalizedCocycle (ι := ι) b)) := by
  ext x
  simp [permActionHom_apply, permCompatibleHom_base, tupleActionHom_apply]

end ProjCompat

/-- The projection from the lifted monomial group to its base. -/
def monomialProjHom {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    (b : SkewBicharacter A B) (ι : Type uι) [Fintype ι] [LinearOrder ι] :
    MonomialLift b ι →* MonomialBase A ι :=
  SemidirectProduct.map
    (NormalizedCocycleExtension.projHom (lowerNormalizedCocycle (ι := ι) b))
    (MonoidHom.id _)
    (fun σ => proj_compat b ι σ)

/-- The inclusion of central coefficients in the lifted monomial group. -/
def monomialInlHom {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    (b : SkewBicharacter A B) (ι : Type uι) [Fintype ι] [LinearOrder ι] :
    Multiplicative B →* MonomialLift b ι :=
  (SemidirectProduct.inl).comp
    (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b))

@[simp]
theorem monomialProjHom_left {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {b : SkewBicharacter A B} {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (x : MonomialLift b ι) :
    (monomialProjHom b ι x).left = x.left.base :=
  rfl

@[simp]
theorem monomialProjHom_right {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {b : SkewBicharacter A B} {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (x : MonomialLift b ι) :
    (monomialProjHom b ι x).right = x.right :=
  rfl

@[simp]
theorem monomialInlHom_left {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {b : SkewBicharacter A B} {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (c : Multiplicative B) :
    (monomialInlHom b ι c).left =
      NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c :=
  rfl

@[simp]
theorem monomialInlHom_right {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {b : SkewBicharacter A B} {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (c : Multiplicative B) :
    (monomialInlHom b ι c).right = 1 :=
  rfl

theorem permActionHom_fix_inl {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (b : SkewBicharacter A B) (σ : Equiv.Perm ι) (c : Multiplicative B) :
    permActionHom (ι := ι) b σ
      (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c) =
      NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c := by
  apply NormalizedCocycleExtension.Extension.ext
  · calc (permActionHom (ι := ι) b σ
          (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c)).base
        = permute σ
            (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c).base := by
            simp [permActionHom_apply, permCompatibleHom_base]
      _ = 1 := by simp [permute_one_tuple]
  · calc (permActionHom (ι := ι) b σ
          (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c)).coeff
        = (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c).coeff *
            Multiplicative.ofAdd (inversionSum (ι := ι) b σ
              (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c).base) := by
            simp [permActionHom_apply, permCompatibleHom_coeff]
      _ = c * Multiplicative.ofAdd (inversionSum (ι := ι) b σ 1) := by rfl
      _ = c * Multiplicative.ofAdd 0 := by rw [inversionSum_one_tuple]
      _ = c := by simp

theorem extension_coeff_central {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (b : SkewBicharacter A B) (c : Multiplicative B) (x : Extension b ι) :
    NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c * x =
      x * NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c := by
  have hCentral : (extensionGroupExtension (ι := ι) b).IsCentral :=
    extension_isCentral (ι := ι) b
  have hKer : NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c ∈
      (extensionGroupExtension (ι := ι) b).rightHom.ker := by
    rw [MonoidHom.mem_ker]; rfl
  have hCenter : NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c ∈
      Subgroup.center (Extension b ι) := hCentral hKer
  exact (Subgroup.mem_center_iff.mp hCenter x).symm

/-- The group extension formed by the actual monomial projection and inclusion. -/
def monomialGroupExtension {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    (b : SkewBicharacter A B) (ι : Type uι) [Fintype ι] [LinearOrder ι] :
    GroupExtension (Multiplicative B) (MonomialLift b ι) (MonomialBase A ι) where
  inl := monomialInlHom b ι
  rightHom := monomialProjHom b ι
  inl_injective := by
    intro c₁ c₂ h
    have hLeft : (monomialInlHom b ι c₁).left = (monomialInlHom b ι c₂).left :=
      congrArg SemidirectProduct.left h
    have hCoeff := congrArg NormalizedCocycleExtension.Extension.coeff hLeft
    simpa using hCoeff
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      rw [MonoidHom.mem_ker]
      apply SemidirectProduct.ext <;> rfl
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : monomialProjHom b ι x = 1 := hx
      have hBase : x.left.base = 1 := by
        calc x.left.base = (monomialProjHom b ι x).left := rfl
          _ = (1 : MonomialBase A ι).left := by rw [hx']
          _ = 1 := rfl
      have hRight : x.right = 1 := by
        calc x.right = (monomialProjHom b ι x).right := rfl
          _ = (1 : MonomialBase A ι).right := by rw [hx']
          _ = 1 := rfl
      have hLeftEq : x.left =
          NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) x.left.coeff := by
        apply NormalizedCocycleExtension.Extension.ext
        · exact hBase
        · rfl
      refine ⟨x.left.coeff, ?_⟩
      apply SemidirectProduct.ext
      · exact hLeftEq.symm
      · exact hRight.symm
  rightHom_surjective := by
    intro y
    refine ⟨⟨⟨y.left, 1⟩, y.right⟩, ?_⟩
    apply SemidirectProduct.ext <;> rfl

theorem monomialExtension_isCentral {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
    {ι : Type uι} [Fintype ι] [LinearOrder ι]
    (b : SkewBicharacter A B) :
    (monomialGroupExtension b ι).IsCentral := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : monomialProjHom b ι x = 1 := hx
  have hBase : x.left.base = 1 := by
    calc x.left.base = (monomialProjHom b ι x).left := rfl
      _ = (1 : MonomialBase A ι).left := by rw [hx']
      _ = 1 := rfl
  have hRight : x.right = 1 := by
    calc x.right = (monomialProjHom b ι x).right := rfl
      _ = (1 : MonomialBase A ι).right := by rw [hx']
      _ = 1 := rfl
  have hLeftEq : x.left =
      NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) x.left.coeff := by
    apply NormalizedCocycleExtension.Extension.ext
    · exact hBase
    · rfl
  have hx_eq : x = monomialInlHom b ι x.left.coeff := by
    apply SemidirectProduct.ext
    · exact hLeftEq
    · exact hRight
  rw [hx_eq, Subgroup.mem_center_iff]
  intro y
  have hFix : permActionHom (ι := ι) b y.right
      (NormalizedCocycleExtension.inlHom
        (lowerNormalizedCocycle (ι := ι) b) x.left.coeff) =
      NormalizedCocycleExtension.inlHom
        (lowerNormalizedCocycle (ι := ι) b) x.left.coeff :=
    permActionHom_fix_inl b y.right x.left.coeff
  have hCent : NormalizedCocycleExtension.inlHom
      (lowerNormalizedCocycle (ι := ι) b) x.left.coeff * y.left =
      y.left * NormalizedCocycleExtension.inlHom
        (lowerNormalizedCocycle (ι := ι) b) x.left.coeff :=
    extension_coeff_central b x.left.coeff y.left
  have hLeft : (monomialInlHom b ι x.left.coeff * y).left =
      (y * monomialInlHom b ι x.left.coeff).left := by
    calc (monomialInlHom b ι x.left.coeff * y).left
        = (NormalizedCocycleExtension.inlHom
            (lowerNormalizedCocycle (ι := ι) b) x.left.coeff) *
            y.left := by simp [SemidirectProduct.mul_left]
      _ = y.left * (NormalizedCocycleExtension.inlHom
            (lowerNormalizedCocycle (ι := ι) b) x.left.coeff) := by
          rw [hCent]
      _ = y.left * (permActionHom (ι := ι) b y.right
            (NormalizedCocycleExtension.inlHom
              (lowerNormalizedCocycle (ι := ι) b) x.left.coeff)) := by
          rw [hFix]
      _ = (y * monomialInlHom b ι x.left.coeff).left := by
          simp [SemidirectProduct.mul_left]
  have hRightEq : (monomialInlHom b ι x.left.coeff * y).right =
      (y * monomialInlHom b ι x.left.coeff).right := by
    simp [SemidirectProduct.mul_right]
  exact (SemidirectProduct.ext hLeft hRightEq).symm

section BaseFunctoriality

variable {A : Type uA} {A' : Type uA'} {ι : Type uι} [Group A] [Group A']

/-- The coefficient map on the monomial base, retaining the coordinate permutation. -/
def monomialBaseHom (f : A →* A') :
    MonomialBase A ι →* MonomialBase A' ι where
  toFun x := ⟨mapTupleHom (ι := ι) f x.left, x.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · simp [mapTuple_one]
    · rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · simp [mapTuple_mul, permute_mapTuple_comm]
    · rfl

@[simp]
theorem monomialBaseHom_left (f : A →* A')
    (x : MonomialBase A ι) :
    (monomialBaseHom (ι := ι) f x).left = mapTupleHom (ι := ι) f x.left :=
  rfl

@[simp]
theorem monomialBaseHom_right (f : A →* A')
    (x : MonomialBase A ι) :
    (monomialBaseHom (ι := ι) f x).right = x.right :=
  rfl

@[simp]
theorem monomialBaseHom_id :
    monomialBaseHom (ι := ι) (MonoidHom.id A) =
      MonoidHom.id (MonomialBase A ι) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp [mapTupleHom_id]
  · rfl

theorem monomialBaseHom_comp {A'' : Type uA''} [Group A'']
    (f : A →* A') (g : A' →* A'') :
    monomialBaseHom (ι := ι) (g.comp f) =
      (monomialBaseHom (ι := ι) g).comp (monomialBaseHom (ι := ι) f) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp [mapTupleHom_comp]
  · rfl

end BaseFunctoriality

section LiftFunctoriality

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  {ι : Type uι} [Group A] [AddCommGroup B] [Group A'] [AddCommGroup B']
  [Fintype ι] [LinearOrder ι]

/-- The induced group homomorphism between the specified monomial lifts. -/
def monomialLiftHom {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') :
    MonomialLift b ι →* MonomialLift b' ι :=
  SemidirectProduct.map (extensionHom (ι := ι) φ) (MonoidHom.id _) (by
    intro σ
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, permActionHom_apply,
      MonoidHom.id_apply]
    exact extensionHom_permCompatibleHom (ι := ι) φ σ x)

@[simp]
theorem monomialLiftHom_left {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (x : MonomialLift b ι) :
    (monomialLiftHom (ι := ι) φ x).left = extensionHom (ι := ι) φ x.left :=
  rfl

@[simp]
theorem monomialLiftHom_right {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (x : MonomialLift b ι) :
    (monomialLiftHom (ι := ι) φ x).right = x.right :=
  rfl

theorem monomialProj_naturality {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') :
    (monomialProjHom b' ι).comp (monomialLiftHom (ι := ι) φ) =
      (monomialBaseHom (ι := ι) φ.source).comp (monomialProjHom b ι) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp [extensionHom_base]
  · rfl

theorem monomialInl_naturality {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') :
    (monomialLiftHom (ι := ι) φ).comp (monomialInlHom b ι) =
      (monomialInlHom b' ι).comp (AddMonoidHom.toMultiplicative φ.target) := by
  apply MonoidHom.ext
  intro c
  apply SemidirectProduct.ext
  · apply NormalizedCocycleExtension.Extension.ext
    · calc (extensionHom (ι := ι) φ
            (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c)).base
          = mapTuple (ι := ι) φ.source
              (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c).base := by
            simp [extensionHom_base]
        _ = mapTuple (ι := ι) φ.source 1 := by rfl
        _ = 1 := by simp [mapTuple_one]
    · calc (extensionHom (ι := ι) φ
            (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c)).coeff
          = (AddMonoidHom.toMultiplicative φ.target)
              (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b) c).coeff := by
            simp [extensionHom_coeff]
        _ = (AddMonoidHom.toMultiplicative φ.target) c := by rfl
        _ = (NormalizedCocycleExtension.inlHom (lowerNormalizedCocycle (ι := ι) b')
              ((AddMonoidHom.toMultiplicative φ.target) c)).coeff := by rfl
  · rfl

@[simp]
theorem monomialLiftHom_id (b : SkewBicharacter A B) :
    monomialLiftHom (ι := ι) (SkewBicharacter.Hom.id b) =
      MonoidHom.id (MonomialLift b ι) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp [extensionHom_id]
  · rfl

theorem monomialLiftHom_comp {A'' : Type uA''} {B'' : Type uB''}
    [Group A''] [AddCommGroup B'']
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'} {b'' : SkewBicharacter A'' B''}
    (f : SkewBicharacter.Hom b b') (g : SkewBicharacter.Hom b' b'') :
    monomialLiftHom (ι := ι) (SkewBicharacter.Hom.comp f g) =
      (monomialLiftHom (ι := ι) g).comp (monomialLiftHom (ι := ι) f) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp [extensionHom_comp]
  · rfl

end LiftFunctoriality

end PermutationBilinearCocycle

end
