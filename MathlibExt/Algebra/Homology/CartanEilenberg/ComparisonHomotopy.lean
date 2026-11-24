/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Comparison
public import MathlibExt.Algebra.Homology.CartanEilenberg.Existence
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Homotopy uniqueness of Cartan--Eilenberg comparisons and the resolution functor

Any two supplied comparisons of Cartan--Eilenberg resolutions over the
same chain map are related by compatible homotopies on the boundary,
homology, cycle, and term resolutions, assembled from uniqueness of
projective-resolution lifts and the endpoint-controlled horseshoe
homotopy.  The term homotopies assemble into a homotopy between the
induced bicomplex maps in the resolution direction: the bicomplex is
regarded as a chain complex in the category of chain complexes, and the
homotopy components in resolution degree are chain maps in the original
degree.  Consequently a supplied comparison has a well-defined image in
the homotopy category, and chosen Cartan--Eilenberg resolutions form a
functor from nonnegative chain complexes to the homotopy category of
chain complexes of chain complexes, in the same way that Mathlib's
`projectiveResolutions` functor arises from projective resolutions of
objects.  No naturality of spectral-sequence pages or edges is claimed.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L L' : ChainComplex C ℕ}
variable (P : CartanEilenbergResolution L) (Q : CartanEilenbergResolution L')
variable (g : L ⟶ L')

namespace CartanEilenbergResolution

namespace Hom

/-- A supplied homotopy between two comparisons of Cartan--Eilenberg
resolutions over the same chain map: homotopies of the four constituent
families, compatible with the horseshoe inclusions and projections.
The cycles compatibility in degree `j` involves the boundary homotopy
in degree `j + 1`, matching the asymmetric endpoints of the cycle
horseshoe. -/
structure ComparisonHomotopy (F G : Hom P Q g) where
  /-- Homotopies of the boundary endpoint lifts. -/
  boundaryHomotopy (j : ℕ) :
    Homotopy (F.boundaryHom j).hom (G.boundaryHom j).hom
  /-- Homotopies of the homology endpoint lifts. -/
  homologyHomotopy (j : ℕ) :
    Homotopy (F.homologyHom j).hom (G.homologyHom j).hom
  /-- Homotopies of the cycle horseshoe comparisons. -/
  cyclesHomotopy (j : ℕ) :
    Homotopy (F.cyclesHom j).hom (G.cyclesHom j).hom
  /-- The cycle homotopies are compatible with the boundary homotopies
  through the cycle horseshoe inclusions. -/
  cycles_comp_i (j a b : ℕ) :
    (P.cyclesHorseshoe j).i.f a ≫ (cyclesHomotopy j).hom a b =
      (boundaryHomotopy (j + 1)).hom a b ≫ (Q.cyclesHorseshoe j).i.f b
  /-- The cycle homotopies are compatible with the homology homotopies
  through the cycle horseshoe projections. -/
  cycles_comp_p (j a b : ℕ) :
    (cyclesHomotopy j).hom a b ≫ (Q.cyclesHorseshoe j).p.f b =
      (P.cyclesHorseshoe j).p.f a ≫ (homologyHomotopy j).hom a b
  /-- Homotopies of the term horseshoe comparisons. -/
  termHomotopy (j : ℕ) :
    Homotopy (F.termHom j).hom (G.termHom j).hom
  /-- The term homotopies are compatible with the cycle homotopies
  through the term horseshoe inclusions. -/
  term_comp_i (j a b : ℕ) :
    (P.termHorseshoe j).i.f a ≫ (termHomotopy j).hom a b =
      (cyclesHomotopy j).hom a b ≫ (Q.termHorseshoe j).i.f b
  /-- The term homotopies are compatible with the boundary homotopies
  through the term horseshoe projections. -/
  term_comp_p (j a b : ℕ) :
    (termHomotopy j).hom a b ≫ (Q.termHorseshoe j).p.f b =
      (P.termHorseshoe j).p.f a ≫ (boundaryHomotopy j).hom a b

/-- Any two supplied comparisons of Cartan--Eilenberg resolutions over
the same chain map are related by a supplied comparison homotopy. -/
theorem nonempty_comparisonHomotopy (F G : Hom P Q g) :
    Nonempty (ComparisonHomotopy P Q g F G) := by
  let βH (j : ℕ) := (F.boundaryHom j).homotopy (G.boundaryHom j)
  let ηH (j : ℕ) := (F.homologyHom j).homotopy (G.homologyHom j)
  have hζ : ∀ j : ℕ, ∃ h : Homotopy (F.cyclesHom j).hom (G.cyclesHom j).hom,
      (∀ a b : ℕ, (P.cyclesHorseshoe j).i.f a ≫ h.hom a b =
        (βH (j + 1)).hom a b ≫ (Q.cyclesHorseshoe j).i.f b) ∧
      ∀ a b : ℕ, h.hom a b ≫ (Q.cyclesHorseshoe j).p.f b =
        (P.cyclesHorseshoe j).p.f a ≫ (ηH j).hom a b := fun j =>
    CategoryTheory.ProjectiveResolution.HorseshoeData.Hom.nonempty_homotopy
      (P.cyclesSpec j) (Q.cyclesSpec j) (βH (j + 1)) (ηH j) (F.cyclesHom j)
      (G.cyclesHom j)
  choose ζH hζe using hζ
  have hτ : ∀ j : ℕ, ∃ h : Homotopy (F.termHom j).hom (G.termHom j).hom,
      (∀ a b : ℕ, (P.termHorseshoe j).i.f a ≫ h.hom a b =
        (ζH j).hom a b ≫ (Q.termHorseshoe j).i.f b) ∧
      ∀ a b : ℕ, h.hom a b ≫ (Q.termHorseshoe j).p.f b =
        (P.termHorseshoe j).p.f a ≫ (βH j).hom a b := fun j =>
    CategoryTheory.ProjectiveResolution.HorseshoeData.Hom.nonempty_homotopy
      (P.termSpec j) (Q.termSpec j) (ζH j) (βH j) (F.termHom j) (G.termHom j)
  choose τH hτe using hτ
  exact ⟨{ boundaryHomotopy := βH,
            homologyHomotopy := ηH,
            cyclesHomotopy := ζH,
            cycles_comp_i := fun j => (hζe j).1,
            cycles_comp_p := fun j => (hζe j).2,
            termHomotopy := τH,
            term_comp_i := fun j => (hτe j).1,
            term_comp_p := fun j => (hτe j).2 }⟩

/-- Two supplied comparisons have homotopic boundary endpoint lifts in
every degree. -/
theorem nonempty_boundaryHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.boundaryHom j).hom (G.boundaryHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.boundaryHomotopy j

/-- Two supplied comparisons have homotopic homology endpoint lifts in
every degree. -/
theorem nonempty_homologyHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.homologyHom j).hom (G.homologyHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.homologyHomotopy j

/-- Two supplied comparisons have homotopic cycle horseshoe comparisons
in every degree. -/
theorem nonempty_cyclesHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.cyclesHom j).hom (G.cyclesHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.cyclesHomotopy j

/-- Two supplied comparisons have homotopic term horseshoe comparisons
in every degree. -/
theorem nonempty_termHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.termHom j).hom (G.termHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.termHomotopy j

namespace ComparisonHomotopy

variable {F G : Hom P Q g} (Θ : ComparisonHomotopy P Q g F G)

set_option backward.isDefEq.respectTransparency false in
/-- The components of the induced bicomplex homotopy, before
assembly: in resolution degrees `(a, b)`, the chain map in the original
degree whose component in degree `j` is the `(a, b)` component of the
term homotopy in that degree.  It is a chain map by the same
three-square pasting as `termDifferential_naturality`, using the
inclusion and projection compatibilities of the comparison homotopy;
off the successor diagonal all components vanish. -/
noncomputable def bicomplexHomotopyHom (a b : ℕ) :
    P.bicomplex.X a ⟶ Q.bicomplex.X b :=
  ChainComplex.ofHom (fun j => (Θ.termHomotopy j).hom a b) (fun j => by
    by_cases hb : a + 1 = b
    · subst hb
      rw [Q.bicomplex_d₂, P.bicomplex_d₂, Q.termDifferential_eq j,
        P.termDifferential_eq j]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [reassoc_of% (Θ.term_comp_p (j + 1) a (a + 1)),
        ← reassoc_of% (Θ.cycles_comp_i j a (a + 1)),
        ← Θ.term_comp_i j a (a + 1)]
    · have hz1 : (Θ.termHomotopy (j + 1)).hom a b = 0 :=
        (Θ.termHomotopy (j + 1)).zero a b hb
      have hz2 : (Θ.termHomotopy j).hom a b = 0 :=
        (Θ.termHomotopy j).zero a b hb
      rw [hz1, hz2]
      simp)

@[simp]
theorem bicomplexHomotopyHom_f (a b j : ℕ) :
    (bicomplexHomotopyHom P Q g Θ a b).f j = (Θ.termHomotopy j).hom a b :=
  rfl

/-- The induced homotopy between the bicomplex maps of two supplied
comparisons, in the resolution direction: the bicomplex is regarded as
a chain complex of chain complexes indexed first by resolution degree. -/
noncomputable def bicomplexHomotopy :
    Homotopy F.bicomplexHom G.bicomplexHom where
  hom a b := bicomplexHomotopyHom P Q g Θ a b
  zero a b h := by
    ext j
    simp only [bicomplexHomotopyHom_f, HomologicalComplex.zero_f_apply]
    exact (Θ.termHomotopy j).zero a b h
  comm a := by
    cases a with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
        ext j
        have hc := (Θ.termHomotopy j).comm 0
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
          at hc
        simp only [zero_add] at hc
        simp only [bicomplexHomotopyHom_f, HomologicalComplex.add_f_apply,
          HomologicalComplex.comp_f, Hom.bicomplexHom_f_f,
          CartanEilenbergResolution.bicomplex_d₁, zero_add]
        exact hc
    | succ a =>
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        ext j
        have hc := (Θ.termHomotopy j).comm (a + 1)
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
          at hc
        simp only [bicomplexHomotopyHom_f, HomologicalComplex.add_f_apply,
          HomologicalComplex.comp_f, Hom.bicomplexHom_f_f,
          CartanEilenbergResolution.bicomplex_d₁]
        exact hc

@[simp]
theorem bicomplexHomotopy_hom_f (a b j : ℕ) :
    ((bicomplexHomotopy P Q g Θ).hom a b).f j = (Θ.termHomotopy j).hom a b :=
  rfl

end ComparisonHomotopy

/-- Any two supplied comparisons of Cartan--Eilenberg resolutions over
the same chain map induce homotopic bicomplex maps, with the homotopy
taken in the resolution direction. -/
theorem nonempty_bicomplexHomotopy (F G : Hom P Q g) :
    Nonempty (Homotopy F.bicomplexHom G.bicomplexHom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ =>
    ComparisonHomotopy.bicomplexHomotopy P Q g Θ

/-- The image in the homotopy category of the bicomplex map induced by
a supplied comparison, where bicomplexes are regarded as chain
complexes, in the resolution direction, of chain complexes. -/
noncomputable def homotopyClass (F : Hom P Q g) :
    (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex ⟶
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj Q.bicomplex :=
  (HomotopyCategory.quotient (ChainComplex C ℕ)
    (ComplexShape.down ℕ)).map F.bicomplexHom

/-- The homotopy class of the induced bicomplex map does not depend on
the supplied comparison. -/
theorem homotopyClass_eq (F G : Hom P Q g) :
    F.homotopyClass = G.homotopyClass :=
  HomotopyCategory.eq_of_homotopy _ _
    (Classical.choice (nonempty_bicomplexHomotopy P Q g F G))

end Hom

/-- The morphism in the homotopy category induced by a chain map
between supplied Cartan--Eilenberg resolutions, defined by choosing a
supplied comparison; it is independent of the choice by
`Hom.homotopyClass_eq`. -/
noncomputable def homotopyClassMap :
    (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex ⟶
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj Q.bicomplex :=
  (Classical.choice (nonempty_hom P Q g)).homotopyClass

/-- The induced homotopy-category morphism is presented by every
supplied comparison. -/
theorem homotopyClassMap_eq (F : Hom P Q g) :
    homotopyClassMap P Q g = F.homotopyClass :=
  Hom.homotopyClass_eq P Q g _ F

/-- The induced homotopy-category morphism of an identity chain map is
the identity. -/
theorem homotopyClassMap_id (P : CartanEilenbergResolution L) :
    homotopyClassMap P P (𝟙 L) =
      𝟙 ((HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex) := by
  rw [homotopyClassMap_eq P P (𝟙 L) (Hom.id P)]
  simp [Hom.homotopyClass]

/-- The induced homotopy-category morphism of a composite chain map is
the composite of the induced morphisms. -/
theorem homotopyClassMap_comp {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''} :
    homotopyClassMap P R (g ≫ h) =
      homotopyClassMap P Q g ≫ homotopyClassMap Q R h := by
  let F : Hom P Q g := Classical.choice (nonempty_hom P Q g)
  let G : Hom Q R h := Classical.choice (nonempty_hom Q R h)
  have eF : homotopyClassMap P Q g = F.homotopyClass :=
    homotopyClassMap_eq P Q g F
  have eG : homotopyClassMap Q R h = G.homotopyClass :=
    homotopyClassMap_eq Q R h G
  rw [homotopyClassMap_eq P R (g ≫ h) (Hom.comp P Q g F G), eF, eG]
  simp [Hom.homotopyClass]

/-- The bicomplexes of any two supplied Cartan--Eilenberg resolutions
of the same chain complex are homotopy equivalent, by comparisons over
the identity in both directions. -/
noncomputable def bicomplexHomotopyEquiv {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    HomotopyEquiv P.bicomplex Q.bicomplex where
  hom := (Classical.choice (nonempty_hom P Q (𝟙 L))).bicomplexHom
  inv := (Classical.choice (nonempty_hom Q P (𝟙 L))).bicomplexHom
  homotopyHomInvId := by
    have h := Classical.choice (Hom.nonempty_bicomplexHomotopy P P (𝟙 L)
      ((Hom.comp P Q (𝟙 L) (Classical.choice (nonempty_hom P Q (𝟙 L)))
        (Classical.choice (nonempty_hom Q P (𝟙 L)))).cast
          (Category.id_comp (𝟙 L)))
      (Hom.id P))
    simpa using h
  homotopyInvHomId := by
    have h := Classical.choice (Hom.nonempty_bicomplexHomotopy Q Q (𝟙 L)
      ((Hom.comp Q P (𝟙 L) (Classical.choice (nonempty_hom Q P (𝟙 L)))
        (Classical.choice (nonempty_hom P Q (𝟙 L)))).cast
          (Category.id_comp (𝟙 L)))
      (Hom.id Q))
    simpa using h

/-- The homotopy classes of the bicomplexes of any two supplied
Cartan--Eilenberg resolutions of the same chain complex are canonically
isomorphic in the homotopy category, by the standard isomorphism
associated to the homotopy equivalence `bicomplexHomotopyEquiv`. -/
noncomputable def homotopyCategoryIso {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex ≅
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj Q.bicomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (bicomplexHomotopyEquiv P Q)

/-- The forward map of `homotopyCategoryIso` is the induced
homotopy-category morphism of the identity chain map. -/
@[simp]
theorem homotopyCategoryIso_hom {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    (homotopyCategoryIso P Q).hom = homotopyClassMap P Q (𝟙 L) :=
  rfl

/-- The inverse map of `homotopyCategoryIso` is the induced
homotopy-category morphism of the identity chain map in the other
direction. -/
@[simp]
theorem homotopyCategoryIso_inv {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    (homotopyCategoryIso P Q).inv = homotopyClassMap Q P (𝟙 L) :=
  rfl

end CartanEilenbergResolution

section Functor

variable [HasProjectiveResolutions C]

/-- Chosen Cartan--Eilenberg resolutions, as a functor from nonnegative
chain complexes to the homotopy category of chain complexes of chain
complexes.  An object is sent to the homotopy class of the bicomplex of
its chosen Cartan--Eilenberg resolution, in the resolution direction,
and a chain map to the homotopy class of any supplied comparison.  This
is the Cartan--Eilenberg analogue of Mathlib's `projectiveResolutions`
functor. -/
noncomputable def cartanEilenbergResolutions (C : Type u) [Category.{v} C]
    [Abelian C] [HasProjectiveResolutions C] :
    ChainComplex C ℕ ⥤
      HomotopyCategory (ChainComplex C ℕ) (ComplexShape.down ℕ) where
  obj L := (HomotopyCategory.quotient (ChainComplex C ℕ)
      (ComplexShape.down ℕ)).obj (CartanEilenbergResolution.of L).bicomplex
  map f := CartanEilenbergResolution.homotopyClassMap
    (CartanEilenbergResolution.of _) (CartanEilenbergResolution.of _) f
  map_id L := CartanEilenbergResolution.homotopyClassMap_id
    (CartanEilenbergResolution.of L)
  map_comp f g := CartanEilenbergResolution.homotopyClassMap_comp
    (CartanEilenbergResolution.of _) (CartanEilenbergResolution.of _) f
    (R := CartanEilenbergResolution.of _) (h := g)

/-- The value of the Cartan--Eilenberg resolution functor on an object
is the homotopy class of the bicomplex of the chosen resolution. -/
theorem cartanEilenbergResolutions_obj (L : ChainComplex C ℕ) :
    (cartanEilenbergResolutions C).obj L =
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj (CartanEilenbergResolution.of L).bicomplex :=
  rfl

/-- The value of the Cartan--Eilenberg resolution functor on a chain
map is presented by every supplied comparison between the chosen
resolutions. -/
theorem cartanEilenbergResolutions_map {L L' : ChainComplex C ℕ}
    (g : L ⟶ L')
    (F : CartanEilenbergResolution.Hom (CartanEilenbergResolution.of L)
      (CartanEilenbergResolution.of L') g) :
    (cartanEilenbergResolutions C).map g =
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).map F.bicomplexHom :=
  CartanEilenbergResolution.homotopyClassMap_eq _ _ _ F

/-- The chosen value of the Cartan--Eilenberg resolution functor is
isomorphic in the homotopy category to the homotopy class of the
bicomplex of any supplied resolution. -/
noncomputable def cartanEilenbergResolutions_obj_iso (L : ChainComplex C ℕ)
    (P : CartanEilenbergResolution L) :
    (cartanEilenbergResolutions C).obj L ≅
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex :=
  CartanEilenbergResolution.homotopyCategoryIso
    (CartanEilenbergResolution.of L) P

end Functor

end HomologicalComplex

end
