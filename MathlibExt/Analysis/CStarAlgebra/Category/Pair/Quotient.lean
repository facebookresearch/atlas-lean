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

public import MathlibExt.Analysis.CStarAlgebra.Category.Pair.Basic
public import MathlibExt.Analysis.CStarAlgebra.Ideal.Map

/-!
# Actual quotient maps and quotient images of C-star pairs

The public maps use the canonical closed-ideal quotient. In the orthogonal-
ideal excision use case, the printed J/K is the actual image q_K(J); K
need not be a subideal of J.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CStarPairCat

/-- **Quotient of a C*-ideal pair.** A C*-ideal pair `(A,J)` consists of a nonunital complex C*-algebra
`A` and a distinguished closed two-sided star ideal `J ⊆ A`. Its quotient `A/J`, with the quotient
C*-norm, is a nonunital complex C*-algebra. -/
def quotientObject (P : CStarPairCat.{u}) : NonUnitalCStarAlgCat.{u} := by
  letI : P.ideal.carrier.IsTwoSided := P.ideal.isTwoSided
  letI : NonUnitalCStarAlgebra P.ideal.Quotient := P.ideal.quotientCStarAlgebra
  exact NonUnitalCStarAlgCat.of P.ideal.Quotient

/-- **Induced homomorphism of pair quotients.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. A morphism `f : (A,J) →
(B,K)` induces the nonunital star homomorphism `A/J → B/K` given by `[a] ↦ [f(a)]`. -/
def quotientMap {P Q : CStarPairCat.{u}} (f : P ⟶ Q) :
    quotientObject P ⟶ quotientObject Q := by
  letI : P.ideal.carrier.IsTwoSided := P.ideal.isTwoSided
  letI : Q.ideal.carrier.IsTwoSided := Q.ideal.isTwoSided
  letI : NonUnitalCStarAlgebra P.ideal.Quotient := P.ideal.quotientCStarAlgebra
  letI : NonUnitalCStarAlgebra Q.ideal.Quotient := Q.ideal.quotientCStarAlgebra
  exact NonUnitalStarSubalgebra.Quotient.map
    P.ideal.carrier Q.ideal.carrier f.hom f.ideal_mem

@[simp]
theorem quotientMap_apply {P Q : CStarPairCat.{u}} (f : P ⟶ Q)
    (a : P.algebra) :
    quotientMap f (Submodule.Quotient.mk a : P.ideal.Quotient) =
      (Submodule.Quotient.mk (f.hom a) : Q.ideal.Quotient) := by
  let : P.ideal.carrier.IsTwoSided := P.ideal.isTwoSided
  let : Q.ideal.carrier.IsTwoSided := Q.ideal.isTwoSided
  exact NonUnitalStarSubalgebra.Quotient.map_mk
    P.ideal.carrier Q.ideal.carrier f.hom f.ideal_mem a

/-- **Quotient functor for C*-ideal pairs.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. The assignment `(A,J) ↦
A/J`, with the homomorphisms induced by ideal-preserving maps, defines a functor to nonunital
complex C*-algebras. -/
def quotientFunctor : CStarPairCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj := quotientObject
  map := quotientMap
  map_id P := by
    let _ : P.ideal.carrier.IsTwoSided := P.ideal.isTwoSided
    let _ : NonUnitalCStarAlgebra P.ideal.Quotient := P.ideal.quotientCStarAlgebra
    apply NonUnitalCStarAlgCat.hom_ext
    intro x
    obtain ⟨a, rfl⟩ := P.ideal.quotientMap_surjective x
    change
      (quotientMap (𝟙 P) :
        P.ideal.Quotient →⋆ₙₐ[ℂ] P.ideal.Quotient) (Submodule.Quotient.mk a) =
          (Submodule.Quotient.mk a : P.ideal.Quotient)
    have h := quotientMap_apply (𝟙 P) a
    change
      (quotientMap (𝟙 P) :
        P.ideal.Quotient →⋆ₙₐ[ℂ] P.ideal.Quotient) (Submodule.Quotient.mk a) =
          (Submodule.Quotient.mk ((𝟙 P : P ⟶ P).hom a) : P.ideal.Quotient) at h
    rw [h]
    rfl
  map_comp {P Q R} f g := by
    let _ : P.ideal.carrier.IsTwoSided := P.ideal.isTwoSided
    let _ : Q.ideal.carrier.IsTwoSided := Q.ideal.isTwoSided
    let _ : R.ideal.carrier.IsTwoSided := R.ideal.isTwoSided
    let _ : NonUnitalCStarAlgebra P.ideal.Quotient := P.ideal.quotientCStarAlgebra
    let _ : NonUnitalCStarAlgebra Q.ideal.Quotient := Q.ideal.quotientCStarAlgebra
    let _ : NonUnitalCStarAlgebra R.ideal.Quotient := R.ideal.quotientCStarAlgebra
    apply NonUnitalCStarAlgCat.hom_ext
    intro x
    obtain ⟨a, rfl⟩ := P.ideal.quotientMap_surjective x
    change
      (quotientMap (f ≫ g) :
        P.ideal.Quotient →⋆ₙₐ[ℂ] R.ideal.Quotient) (Submodule.Quotient.mk a) =
          (quotientMap g : Q.ideal.Quotient →⋆ₙₐ[ℂ] R.ideal.Quotient)
            ((quotientMap f : P.ideal.Quotient →⋆ₙₐ[ℂ] Q.ideal.Quotient)
              (Submodule.Quotient.mk a))
    have hfg := quotientMap_apply (f ≫ g) a
    have hf := quotientMap_apply f a
    have hg := quotientMap_apply g (f.hom a)
    change
      (quotientMap (f ≫ g) :
        P.ideal.Quotient →⋆ₙₐ[ℂ] R.ideal.Quotient) (Submodule.Quotient.mk a) =
          (Submodule.Quotient.mk ((f ≫ g).hom a) : R.ideal.Quotient) at hfg
    change
      (quotientMap f :
        P.ideal.Quotient →⋆ₙₐ[ℂ] Q.ideal.Quotient) (Submodule.Quotient.mk a) =
          (Submodule.Quotient.mk (f.hom a) : Q.ideal.Quotient) at hf
    change
      (quotientMap g :
        Q.ideal.Quotient →⋆ₙₐ[ℂ] R.ideal.Quotient)
          (Submodule.Quotient.mk (f.hom a)) =
            (Submodule.Quotient.mk (g.hom (f.hom a)) : R.ideal.Quotient) at hg
    rw [hfg, hf, hg]
    rfl

/-- **Natural projection to the quotient pair.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. The quotient projections
give a natural pair morphism `(A,A) → (A/J,A/J)`. -/
def quotientNat :
    NatTrans (forget.{u} ⋙ diagonal) (quotientFunctor ⋙ diagonal) where
  app P :=
    { hom := P.ideal.quotientMap
      ideal_mem := fun _ _ => ClosedStarIdeal.mem_top _ }
  naturality {P Q} f := by
    apply Hom.ext
    ext a
    exact (quotientMap_apply f a).symm

@[simp]
theorem quotientNat_apply (P : CStarPairCat.{u}) (a : P.algebra) :
    Hom.hom (P := diagonal.obj (forget.obj P))
      (Q := diagonal.obj (quotientFunctor.obj P)) (quotientNat.app P) a =
        (Submodule.Quotient.mk a : P.ideal.Quotient) := by
  rfl

/-- **Image pair in a further quotient.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. For a closed two-sided star
ideal `K ⊆ A`, the pair `(A/K,q_K(J))` has the image of `J` as its distinguished closed star ideal. -/
def quotientImage (P : CStarPairCat.{u}) (K : ClosedStarIdeal P.algebra) :
    CStarPairCat.{u} := by
  letI : K.carrier.IsTwoSided := K.isTwoSided
  letI : NonUnitalCStarAlgebra K.Quotient := K.quotientCStarAlgebra
  exact
    { algebra := quotientObject ⟨P.algebra, K⟩
      ideal := ClosedStarIdeal.mapOfSurjective
        K.quotientMap K.quotientMap_surjective P.ideal }

/-- **Pair map to a quotient image.** A C*-ideal pair `(A,J)` consists of a nonunital complex C*-algebra
`A` and a distinguished closed two-sided star ideal `J ⊆ A`. For a closed two-sided star ideal `K ⊆
A`, the quotient map gives a pair morphism `(A,J) → (A/K,q_K(J))`. -/
def quotientImageMap (P : CStarPairCat.{u}) (K : ClosedStarIdeal P.algebra) :
    P ⟶ quotientImage P K := by
  letI : K.carrier.IsTwoSided := K.isTwoSided
  letI : NonUnitalCStarAlgebra K.Quotient := K.quotientCStarAlgebra
  change Hom P
    { algebra := NonUnitalCStarAlgCat.of K.Quotient
      ideal := ClosedStarIdeal.mapOfSurjective
        K.quotientMap K.quotientMap_surjective P.ideal }
  exact
    { hom := K.quotientMap
      ideal_mem := ClosedStarIdeal.mapsTo_mapOfSurjective
        K.quotientMap K.quotientMap_surjective P.ideal }

@[simp]
theorem quotientImageMap_apply (P : CStarPairCat.{u})
    (K : ClosedStarIdeal P.algebra) (a : P.algebra) :
    (quotientImageMap P K).hom a = K.quotientMap a := by
  rfl

/-- **Orthogonality of closed star ideals.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. For another closed two-sided
star ideal `K ⊆ A`, this means that every product `j k` with `j ∈ J` and `k ∈ K` is zero. -/
def IdealsOrthogonal (P : CStarPairCat.{u}) (K : ClosedStarIdeal P.algebra) : Prop :=
  ∀ a ∈ P.ideal, ∀ b ∈ K, a * b = 0

end CStarPairCat
