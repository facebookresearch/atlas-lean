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
# Relative Hochschild and bar kernels

For a two-sided nonunital k-subalgebra I of A, the quotient map A → A/I induces maps of the
naive Hochschild b-complex and bar b′-complex. Their kernels are the relative complexes. The
ideal inclusion maps into each kernel because its composite with the quotient is zero.

An arbitrary ground module V can be tensored with the bar words, keeping identity on V under
the algebra quotient. Positive bar placement shifts a word of length n + 1 into degree n + 1
and has a zero degree-zero term. Its relative quotient kernel therefore has a word map into V
⊗[k] A^⊗(n+1) in those degrees.

All maps are built from the quotient and tensor functors; the coefficient V does not require a
flatness assumption.
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

/-- Let k be commutative and M, N k-modules in a common carrier universe. For n : ℕ,
TensorPower.consLevelMap (0 : M →ₗ[k] N) n = 0. Its distinguished first tensor factor is
mapped by zero, including at n = 0. -/
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

/-- Let k be commutative and A, B nonunital k-algebra rings in a common carrier universe, with
k-bilinear multiplication. Then cyclicBComplexHom (0 : A →ₙₐ[k] B) = 0; every degree map has a
zero distinguished tensor factor. -/
theorem cyclicBComplexHom_zero_original : cyclicBComplexHom (0 : A →ₙₐ[k] B) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [cyclicBComplexHom_f]
  change ModuleCat.ofHom (TensorPower.consLevelMap (0 : A →ₗ[k] B) n) = 0
  rw [originalConsWordMap_zero]
  rfl

/-- For nonunital k-algebra rings A, B, C in a common carrier universe and maps f : A →ₙₐ[k] B, g
: B →ₙₐ[k] C, barAlgebraComplexMap (g.comp f) = barAlgebraComplexMap f ≫ barAlgebraComplexMap
g. -/
theorem barAlgebraComplexMap_comp_original (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] C) :
    barAlgebraComplexMap (g.comp f) = barAlgebraComplexMap f ≫ barAlgebraComplexMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change TensorPower.consLevelMap ((g : B →ₗ[k] C).comp (f : A →ₗ[k] B)) n =
    (TensorPower.consLevelMap (g : B →ₗ[k] C) n).comp (TensorPower.consLevelMap (f : A →ₗ[k] B) n)
  exact (TensorPower.consLevelMap_comp (f : A →ₗ[k] B) (g : B →ₗ[k] C) n).symm

/-- For nonunital k-algebra rings A, B over a commutative k, with common carrier universe and
k-bilinear multiplication, barAlgebraComplexMap (0 : A →ₙₐ[k] B) = 0. -/
theorem barAlgebraComplexMap_zero_original : barAlgebraComplexMap (0 : A →ₙₐ[k] B) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change ModuleCat.ofHom (TensorPower.consLevelMap (0 : A →ₗ[k] B) n) = 0
  rw [originalConsWordMap_zero]
  rfl

end OriginalAlgebraMaps

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. relativeNaiveComplex is
kernel(cyclicBComplexHom I.quotientMap), a chain complex indexed by ℕ with the restricted b
differential. -/
abbrev relativeNaiveComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  kernel (cyclicBComplexHom I.quotientMap)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. The induced map
bComplex(I) → bComplex(A) has zero quotient composite. Its kernel lift defines
idealToRelativeNaiveComplex : bComplex(I) ⟶ relativeNaiveComplex. -/
def idealToRelativeNaiveComplex : bComplex k I.Algebra ⟶ relativeNaiveComplex k A I :=
  kernel.lift (cyclicBComplexHom I.quotientMap) (cyclicBComplexHom I.subtypeHom) (by
    rw [← cyclicBComplexHom_comp, I.quotientMap_comp_inclusion, cyclicBComplexHom_zero_original])

@[reassoc]
theorem idealToRelativeNaiveComplex_ι :
    idealToRelativeNaiveComplex k A I ≫ kernel.ι (cyclicBComplexHom I.quotientMap) =
      cyclicBComplexHom I.subtypeHom := kernel.lift_ι _ _ _

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. relativeBarComplex is the kernel of barAlgebraMap
I.quotientMap on the V-coefficient bar complexes. The quotient map is identity on V and
applies A → Q to every algebra factor. -/
abbrev relativeBarComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  kernel (barAlgebraMap (V := V) I.quotientMap)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. barAlgebraMap I.subtypeHom ≫ barAlgebraMap
I.quotientMap = 0 as a map from the V-coefficient bar complex of I to that of Q. -/
theorem barIdeal_quotient_zero :
    barAlgebraMap (V := V) I.subtypeHom ≫ barAlgebraMap (V := V) I.quotientMap = 0 := by
  let F := ((ModuleCat.tensorBifunctorAt k).obj (ModuleCat.of k V)).mapHomologicalComplex
    (ComplexShape.down ℕ)
  change F.map (barAlgebraComplexMap I.subtypeHom) ≫ F.map (barAlgebraComplexMap I.quotientMap) = 0
  rw [← F.map_comp, ← barAlgebraComplexMap_comp_original, I.quotientMap_comp_inclusion,
    barAlgebraComplexMap_zero_original, Functor.map_zero]

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. The zero composite of ideal inclusion with quotient
gives a kernel lift idealToRelativeBarComplex : barComplex k I V ⟶ relativeBarComplex k A I V. -/
def idealToRelativeBarComplex : barComplex k I.Algebra V ⟶ relativeBarComplex k A I V :=
  kernel.lift (barAlgebraMap (V := V) I.quotientMap) (barAlgebraMap (V := V) I.subtypeHom)
    (barIdeal_quotient_zero k A I V)

@[reassoc]
theorem idealToRelativeBarComplex_ι :
    idealToRelativeBarComplex k A I V ≫ kernel.ι (barAlgebraMap (V := V) I.quotientMap) =
      barAlgebraMap (V := V) I.subtypeHom := kernel.lift_ι _ _ _

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. positiveBarComplex is barComplex k A V extended along
the shape embedding n ↦ n + 1. Its degree n + 1 has carrier V ⊗[k] A^⊗(n+1), and degree zero
is a zero object. -/
abbrev positiveBarComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (barComplex k A V).extend (ComplexShape.embeddingDown'Add (1 : ℕ) 1)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. For n : ℕ, positiveBarWordIso identifies
(positiveBarComplex k A V).X (n + 1) with ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A),
using the extension-degree and tensor first-factor equivalences. -/
def positiveBarWordIso (n : ℕ) :
    (positiveBarComplex k A V).X (n + 1) ≅ ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) :=
  (barComplex k A V).extendXIso (ComplexShape.embeddingDown'Add (1 : ℕ) 1) rfl ≪≫
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toModuleIso

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. The object (positiveBarComplex k A V).X 0 is zero
because degree zero lies outside the image of the embedding n ↦ n + 1. -/
theorem positiveBarComplex_isZero_zero : IsZero ((positiveBarComplex k A V).X 0) :=
  (barComplex k A V).isZero_extend_X (ComplexShape.embeddingDown'Add (1 : ℕ) 1) 0
    (fun n => by change n + 1 ≠ 0; exact Nat.succ_ne_zero n)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. positiveBarQuotientMap : positiveBarComplex A V ⟶
positiveBarComplex Q V is the extension of the coefficient bar quotient map along n ↦ n + 1. -/
abbrev positiveBarQuotientMap : positiveBarComplex k A V ⟶ positiveBarComplex k I.Quotient V :=
  HomologicalComplex.extendMap (barAlgebraMap (V := V) I.quotientMap)
    (ComplexShape.embeddingDown'Add (1 : ℕ) 1)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. relativePositiveBarComplex is
kernel(positiveBarQuotientMap k A I V), retaining positive word-length grading and the passive
ground coefficient V. -/
abbrev relativePositiveBarComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  kernel (positiveBarQuotientMap k A I V)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Let V be an arbitrary
k-module in a separate carrier universe. For n : ℕ, relativePositiveBarWordMap maps the
relative kernel's degree n + 1 into V ⊗[k] TensorPower k (n + 1) A. It is the component kernel
inclusion followed by positiveBarWordIso. -/
def relativePositiveBarWordMap (n : ℕ) :
    (relativePositiveBarComplex k A I V).X (n + 1) →ₗ[k]
      V ⊗[k] TensorPower k (n + 1) A :=
  (positiveBarWordIso k A V n).hom.hom.comp
    ((kernel.ι (positiveBarQuotientMap k A I V)).f (n + 1)).hom

end ModuleCat.Algebra.Hochschild.NonUnital
