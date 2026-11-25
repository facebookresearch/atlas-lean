/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Algebra.NonUnitalIdeal
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitalSBI
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.BarCoefficients
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Relative bar and naive Hochschild kernels

The nonunital quotient maps induce kernels
of the b′ and b complexes with arbitrary
coefficient V. Positive bar placement uses
word length n + 1 in degree n + 1 and
a zero augmentation term.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

section OriginalWordMaps

variable (k : Type u) [CommRing k] (M N : Type v) [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

/-- The original cons tensor map of a zero linear map is zero because its first factor is zero. -/
theorem originalConsWordMap_zero (n : ℕ) :
    TensorPower.consLevelMap (0 : M →ₗ[k] N) n = 0 := by
  dsimp only [TensorPower.consLevelMap]
  exact TensorProduct.map_zero_left _

end OriginalWordMaps

section OriginalAlgebraMaps

variable {k : Type u} [CommRing k] {A B C : Type v}
  [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [NonUnitalRing B] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
  [NonUnitalRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]

/-- The original naive Hochschild map sends the original zero algebra map to zero. -/
theorem cyclicBComplexHom_zero_original : cyclicBComplexHom (0 : A →ₙₐ[k] B) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [cyclicBComplexHom_f]
  change ModuleCat.ofHom (TensorPower.consLevelMap (0 : A →ₗ[k] B) n) = 0
  rw [originalConsWordMap_zero]
  rfl

/-- The original bar algebra maps retain composition through their original tensor maps. -/
theorem barAlgebraComplexMap_comp_original (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] C) :
    barAlgebraComplexMap (g.comp f) = barAlgebraComplexMap f ≫ barAlgebraComplexMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change TensorPower.consLevelMap ((g : B →ₗ[k] C).comp (f : A →ₗ[k] B)) n =
    (TensorPower.consLevelMap (g : B →ₗ[k] C) n).comp (TensorPower.consLevelMap (f : A →ₗ[k] B) n)
  exact (TensorPower.consLevelMap_comp (f : A →ₗ[k] B) (g : B →ₗ[k] C) n).symm

/-- The same original zero tensor map gives the zero bar chain map. -/
theorem barAlgebraComplexMap_zero_original : barAlgebraComplexMap (0 : A →ₙₐ[k] B) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change ModuleCat.ofHom (TensorPower.consLevelMap (0 : A →ₗ[k] B) n) = 0
  rw [originalConsWordMap_zero]
  rfl

end OriginalAlgebraMaps

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The naive-Hochschild quotient kernel, with the original b differential. -/
abbrev relativeNaiveComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  kernel (cyclicBComplexHom I.quotientMap)

/-- The original ideal inclusion lands in the naive quotient kernel. -/
def idealToRelativeNaiveComplex : bComplex k I.Algebra ⟶ relativeNaiveComplex k A I :=
  kernel.lift (cyclicBComplexHom I.quotientMap) (cyclicBComplexHom I.subtypeHom) (by
    rw [← cyclicBComplexHom_comp, I.quotientMap_comp_inclusion, cyclicBComplexHom_zero_original])

@[reassoc]
theorem idealToRelativeNaiveComplex_ι :
    idealToRelativeNaiveComplex k A I ≫ kernel.ι (cyclicBComplexHom I.quotientMap) =
      cyclicBComplexHom I.subtypeHom := kernel.lift_ι _ _ _

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- The arbitrary-coefficient bar kernel uses the original coefficient identity and quotient. -/
abbrev relativeBarComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  kernel (barAlgebraMap (V := V) I.quotientMap)

/-- The original coefficient bar ideal map has zero quotient composite by the native tensor functor. -/
theorem barIdeal_quotient_zero :
    barAlgebraMap (V := V) I.subtypeHom ≫ barAlgebraMap (V := V) I.quotientMap = 0 := by
  let F := ((ModuleCat.tensorBifunctorAt k).obj (ModuleCat.of k V)).mapHomologicalComplex
    (ComplexShape.down ℕ)
  change F.map (barAlgebraComplexMap I.subtypeHom) ≫ F.map (barAlgebraComplexMap I.quotientMap) = 0
  rw [← F.map_comp, ← barAlgebraComplexMap_comp_original, I.quotientMap_comp_inclusion,
    barAlgebraComplexMap_zero_original, Functor.map_zero]

/-- The original arbitrary-coefficient ideal map lands in the bar quotient kernel. -/
def idealToRelativeBarComplex : barComplex k I.Algebra V ⟶ relativeBarComplex k A I V :=
  kernel.lift (barAlgebraMap (V := V) I.quotientMap) (barAlgebraMap (V := V) I.subtypeHom)
    (barIdeal_quotient_zero k A I V)

@[reassoc]
theorem idealToRelativeBarComplex_ι :
    idealToRelativeBarComplex k A I V ≫ kernel.ι (barAlgebraMap (V := V) I.quotientMap) =
      barAlgebraMap (V := V) I.subtypeHom := kernel.lift_ι _ _ _

/-- Native positive word-length placement of the original arbitrary-coefficient bar. -/
abbrev positiveBarComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (barComplex k A V).extend (ComplexShape.embeddingDown'Add (1 : ℕ) 1)

/-- Its original degree n+1 has precisely the original coefficient and n+1 algebra word entries. -/
def positiveBarWordIso (n : ℕ) :
    (positiveBarComplex k A V).X (n + 1) ≅ ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) :=
  (barComplex k A V).extendXIso (ComplexShape.embeddingDown'Add (1 : ℕ) 1) rfl ≪≫
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toModuleIso

/-- The zero augmentation is the missing degree-zero object. -/
theorem positiveBarComplex_isZero_zero : IsZero ((positiveBarComplex k A V).X 0) :=
  (barComplex k A V).isZero_extend_X (ComplexShape.embeddingDown'Add (1 : ℕ) 1) 0
    (fun n => by change n + 1 ≠ 0; exact Nat.succ_ne_zero n)

/-- The original quotient map in positive source word-length grading. -/
abbrev positiveBarQuotientMap : positiveBarComplex k A V ⟶ positiveBarComplex k I.Quotient V :=
  HomologicalComplex.extendMap (barAlgebraMap (V := V) I.quotientMap)
    (ComplexShape.embeddingDown'Add (1 : ℕ) 1)

/-- The source word-length quotient kernel has no freely supplied model. -/
abbrev relativePositiveBarComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  kernel (positiveBarQuotientMap k A I V)

/-- Its original source word map retains the kernel inclusion and coefficient V. -/
def relativePositiveBarWordMap (n : ℕ) :
    (relativePositiveBarComplex k A I V).X (n + 1) →ₗ[k]
      V ⊗[k] TensorPower k (n + 1) A :=
  (positiveBarWordIso k A V n).hom.hom.comp
    ((kernel.ι (positiveBarQuotientMap k A I V)).f (n + 1)).hom

end ModuleCat.Algebra.Hochschild.NonUnital
