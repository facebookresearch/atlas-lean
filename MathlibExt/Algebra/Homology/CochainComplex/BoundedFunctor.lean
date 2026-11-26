/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Functors and natural comparisons on bounded cochain complexes

Let C,D be categories with zero morphisms and F : C → D preserve zero morphisms. Its
degreewise cochain prolongation restricts to bounded complexes. Natural transformations and
isomorphisms between such functors restrict with the same component maps in each integer
degree.

The bounded lifts have the canonical identity and composition isomorphisms. A fully faithful
zero-preserving functor reflects boundedness, and an equivalence whose forward functor
preserves zero morphisms induces an equivalence of bounded cochain categories with degreewise
unit and counit.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uE vE

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E]

namespace Functor

variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Let C,D have zero morphisms and F : C → D preserve them. For K ∈ Bounded C and i,j ∈ ℤ, the
differential of the bounded image F(K) from i to j equals F(d_K^{i,j}). -/
theorem mapCochainComplexBounded_obj_d (K : CochainComplex.Bounded C) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj K).obj.d i j = F.map (K.obj.d i j) := rfl

/-- For a zero-preserving functor F : C → D, there is a natural isomorphism F_B ⋙ ι_D ≅ ι_C ⋙
F_cochain. Here F_B is its bounded lift, ι includes bounded complexes into integer cochains,
and F_cochain is degreewise prolongation. Both routes have the same underlying cochain objects
and maps. -/
def mapCochainComplexBoundedCompιIso :
    F.mapCochainComplexBounded ⋙ CochainComplex.Bounded.ι D ≅
      CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex (.up ℤ) := Iso.refl _

/-- Let C,D have zero morphisms and F : C → D be full, faithful, and zero-preserving. An integer
cochain complex F(K), obtained by applying F degreewise, is bounded if and only if K is
bounded. Zero terms are preserved and reflected, so the same integer support windows apply. -/
theorem bounded_mapHomologicalComplex_obj_iff [F.Full] [F.Faithful]
    (K : CochainComplex C ℤ) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (.up ℤ)).obj K) ↔
      CochainComplex.bounded C K := by
  constructor
  · rintro ⟨a, b, hK⟩
    exact ⟨a, b, fun j hj => IsZero.of_full_of_faithful_of_isZero F (K.X j) (hK j hj)⟩
  · exact bounded_mapHomologicalComplex_obj F K

end Functor

namespace NatTrans

variable {F G H : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [H.PreservesZeroMorphisms]

/-- Let C,D have zero morphisms, F,G : C → D preserve them, and τ : F → G be a natural
transformation. Its degreewise cochain transformation restricts to τ_B : F_B → G_B on bounded
complexes. At K its component has jth map τ_{K^j}. -/
def mapCochainComplexBounded (τ : F ⟶ G) :
    F.mapCochainComplexBounded ⟶ G.mapCochainComplexBounded where
  app K := ObjectProperty.homMk ((τ.mapHomologicalComplex (.up ℤ)).app K.obj)
  naturality K L f := by
    apply ObjectProperty.hom_ext
    exact (τ.mapHomologicalComplex (.up ℤ)).naturality f.hom

/-- For zero-preserving functors F,G : C → D, a natural transformation τ : F → G, K ∈ Bounded C,
and j ∈ ℤ, the jth component of τ_B(K) equals τ_{K^j}. -/
theorem mapCochainComplexBounded_app_f (τ : F ⟶ G) (K : CochainComplex.Bounded C) (j : ℤ) :
    ((τ.mapCochainComplexBounded).app K).hom.f j = τ.app (K.obj.X j) := rfl

/-- Let C,D have zero morphisms and F : C → D preserve them. Restricting the identity
transformation of F to bounded cochains gives the identity of its bounded lift F_B. -/
@[simp]
theorem mapCochainComplexBounded_id :
    mapCochainComplexBounded (𝟙 F) = 𝟙 F.mapCochainComplexBounded := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun τ => τ.app K.obj) (mapHomologicalComplex_id (.up ℤ) F)

/-- For zero-preserving functors F,G,H : C → D and natural transformations τ : F → G and σ : G →
H, the bounded restrictions satisfy (τ≫σ)_B = τ_B≫σ_B. The composition is evaluated in every
integer degree of the same bounded complex. -/
theorem mapCochainComplexBounded_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    (τ ≫ σ).mapCochainComplexBounded = τ.mapCochainComplexBounded ≫ σ.mapCochainComplexBounded := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun τ => τ.app K.obj) (mapHomologicalComplex_comp (.up ℤ) τ σ)

end NatTrans

namespace NatIso

variable {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- Let C,D have zero morphisms, F,G : C → D preserve them, and e : F ≅ G. The degreewise
restrictions of e.hom and e.inv give a natural isomorphism F_B ≅ G_B on bounded integer
cochains. -/
def mapCochainComplexBounded (e : F ≅ G) :
    F.mapCochainComplexBounded ≅ G.mapCochainComplexBounded where
  hom := e.hom.mapCochainComplexBounded
  inv := e.inv.mapCochainComplexBounded
  hom_inv_id := by
    rw [← NatTrans.mapCochainComplexBounded_comp, e.hom_inv_id,
      NatTrans.mapCochainComplexBounded_id]
  inv_hom_id := by
    rw [← NatTrans.mapCochainComplexBounded_comp, e.inv_hom_id,
      NatTrans.mapCochainComplexBounded_id]

/-- For zero-preserving functors F,G : C → D, e : F ≅ G, K ∈ Bounded C, and j ∈ ℤ, the jth forward
component of the bounded comparison is e.hom_{K^j}. -/
theorem mapCochainComplexBounded_hom_app_f (e : F ≅ G) (K : CochainComplex.Bounded C) (j : ℤ) :
    ((NatIso.mapCochainComplexBounded e).hom.app K).hom.f j = e.hom.app (K.obj.X j) := rfl

/-- Let F,G : C → D preserve zero morphisms, e : F ≅ G, K ∈ Bounded C, and j ∈ ℤ. The jth inverse
component of the bounded natural isomorphism equals e.inv_{K^j}. -/
theorem mapCochainComplexBounded_inv_app_f (e : F ≅ G) (K : CochainComplex.Bounded C) (j : ℤ) :
    ((NatIso.mapCochainComplexBounded e).inv.app K).hom.f j = e.inv.app (K.obj.X j) := rfl

end NatIso

namespace Functor

/-- Let C,D,E have zero morphisms, F : C → D and G : D → E preserve them. There is a natural
isomorphism F_B ⋙ G_B ≅ (F⋙G)_B. It is the bounded restriction of the degreewise cochain
composition comparison, oriented from successive prolongation to prolongation of the
composite. -/
def mapCochainComplexBoundedCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    F.mapCochainComplexBounded ⋙ G.mapCochainComplexBounded ≅
      (F ⋙ G).mapCochainComplexBounded :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.naturality f.hom)

/-- For a category C with zero morphisms, the bounded lift of Id_C is naturally isomorphic to
Id_{Bounded C}. The comparison is the restriction of the degreewise identity cochain
isomorphism. -/
def mapCochainComplexBoundedIdIso :
    (𝟭 C).mapCochainComplexBounded ≅ 𝟭 (CochainComplex.Bounded C) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((mapHomologicalComplexIdIso C (.up ℤ)).app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (mapHomologicalComplexIdIso C (.up ℤ)).hom.naturality f.hom)

end Functor

namespace Equivalence

variable (e : C ≌ D) [e.functor.PreservesZeroMorphisms]

/-- Let C,D have zero morphisms and e : C ≌ D be an equivalence whose forward functor preserves
zero morphisms. Degreewise prolongation induces Bounded C ≌ Bounded D, because the forward
functor preserves and reflects finite term support. Its inverse is the bounded lift of
e.inverse. -/
def mapCochainComplexBounded : CochainComplex.Bounded C ≌ CochainComplex.Bounded D :=
  (e.mapHomologicalComplex (.up ℤ)).congrFullSubcategory (by
    ext K
    exact e.functor.bounded_mapHomologicalComplex_obj_iff K)

/-- For an equivalence e : C ≌ D with zero-preserving forward functor, the forward functor of its
induced bounded-cochain equivalence equals e.functor_B. In degree j it applies e.functor to
the term and component map. -/
theorem mapCochainComplexBounded_functor :
    e.mapCochainComplexBounded.functor = e.functor.mapCochainComplexBounded := rfl

/-- Let e : C ≌ D have zero-preserving forward functor between categories with zero morphisms. The
inverse of its bounded-cochain equivalence is the bounded lift of e.inverse, acting degreewise
on D-cochains. -/
theorem mapCochainComplexBounded_inverse :
    e.mapCochainComplexBounded.inverse = e.inverse.mapCochainComplexBounded := rfl

/-- Let C,D have zero morphisms and e : C ≌ D have zero-preserving forward functor. For K ∈
Bounded C and j ∈ ℤ, the jth forward component of the bounded unit equals e.unitIso.hom at K^j
: K^j → e.inverse(e.functor(K^j)). -/
theorem mapCochainComplexBounded_unitIso_hom_app_f (K : CochainComplex.Bounded C) (j : ℤ) :
    ((e.mapCochainComplexBounded).unitIso.hom.app K).hom.f j =
      e.unitIso.hom.app (K.obj.X j) := by
  simp [mapCochainComplexBounded, mapHomologicalComplex]
  rfl

/-- Let C,D have zero morphisms and e : C ≌ D have zero-preserving forward functor. For K ∈
Bounded D and j ∈ ℤ, the jth forward component of the bounded counit equals e.counitIso.hom at
K^j : e.functor(e.inverse(K^j)) → K^j. -/
theorem mapCochainComplexBounded_counitIso_hom_app_f (K : CochainComplex.Bounded D) (j : ℤ) :
    ((e.mapCochainComplexBounded).counitIso.hom.app K).hom.f j =
      e.counitIso.hom.app (K.obj.X j) := by
  simp [mapCochainComplexBounded, mapHomologicalComplex]
  rfl

end Equivalence

end CategoryTheory

end
