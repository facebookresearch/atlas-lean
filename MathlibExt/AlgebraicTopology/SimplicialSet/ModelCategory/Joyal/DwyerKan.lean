/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.HoInverse
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence

/-!
# Categorical equivalences and Dwyer–Kan conditions

For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. A homotopy inverse is a
reverse map g:Y→X with isomorphisms [f≫g]≅[id_X] in ho(X^X) and [g≫f]≅[id_Y] in ho(Y^Y). It
implies categorical equivalence, and the converse holds for quasicategories X,Y.

For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. Dwyer–Kan essential
surjectivity is essential surjectivity of ho(f):ho(X)→ho(Y). Full faithfulness requires each
|f_{a,b}| to be a weak homotopy equivalence. A Dwyer–Kan equivalence satisfies both conditions;
they are defined for arbitrary simplicial sets. Kan mapping spaces allow the full-faithfulness
condition to be expressed using simplicial weak equivalences.

References: D. Stevenson, Notes on the Joyal model structure, arXiv:1810.05233; J. Lurie, Higher
Topos Theory, §1.2.2. The mapping-space model here is the right join-slice model.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}

/-!
## Objects and composition in homotopy categories of functor objects

Objects of ho(C^Z) are represented by maps Z→C. Precomposition sends a representative m:B→C to
f≫m, while postcomposition sends m:A→B to m≫q.
-/

/-- For simplicial sets Z,C in universe u, every object a of ho(C^Z) has the form [m] for a
simplicial map m:Z→C, regarded as the corresponding vertex of the internal hom C^Z. -/
private lemma exists_eq_mk_ihomVertexEquiv {Z C : SSet.{u}}
    (a : ((ihom Z).obj C).HomotopyCategory) :
    ∃ m : Z ⟶ C, a = HomotopyCategory.mk (ihomVertexEquiv Z C m) := by
  refine ⟨(ihomVertexEquiv Z C).symm (HomotopyCategory.objEquiv a), ?_⟩
  rw [Equiv.apply_symm_apply]
  exact (HomotopyCategory.objEquiv.left_inv a).symm

/-- For A,B,C in universe u, f:A→B and m:B→C, the induced precomposition functor ho(C^B)→ho(C^A)
sends [m] to [f≫m]. -/
private lemma hoPre_obj_mk_ihomVertexEquiv {A B C : SSet.{u}} (f : A ⟶ B)
    (m : B ⟶ C) :
    (hoFunctor.map ((pre f).app C)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv B C m)) =
      HomotopyCategory.mk (ihomVertexEquiv A C (f ≫ m)) := by
  change (mapHomotopyCategory ((pre f).app C)).obj _ = _
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_pre_app]

/-- For A,B,C in universe u, m:A→B and q:B→C, the induced postcomposition functor ho(B^A)→ho(C^A)
sends [m] to [m≫q]. -/
private lemma hoPost_obj_mk_ihomVertexEquiv {A B C : SSet.{u}} (m : A ⟶ B)
    (q : B ⟶ C) :
    (hoFunctor.map ((ihom A).map q)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv A B m)) =
      HomotopyCategory.mk (ihomVertexEquiv A C (m ≫ q)) := by
  change (mapHomotopyCategory ((ihom A).map q)).obj _ = _
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_ihom_map]

/-!
## Reverse maps with two inverse isomorphisms

For quasicategories X,Y, a categorical f:X→Y admits g:Y→X with equivalence edges from f≫g to
id_X in X^X and from g≫f to id_Y in Y^Y.
-/

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. If f admits g:Y→X with
[f≫g]≅[id_X] in ho(X^X) and [g≫f]≅[id_Y] in ho(Y^Y), then f is categorical. -/
theorem HasHoInverse.categoricalEquivalences (h : HasHoInverse f) :
    categoricalEquivalences f := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := h
  exact categoricalEquivalences.of_hoCompIso g α β

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. For quasicategories X,Y,
f is categorical if and only if there is g:Y→X with [f≫g]≅[id_X] in ho(X^X) and [g≫f]≅[id_Y] in
ho(Y^Y). -/
theorem categoricalEquivalences_iff_hasHoInverse [Quasicategory X]
    [Quasicategory Y] :
    categoricalEquivalences f ↔ HasHoInverse f :=
  ⟨fun hf ↦ hf.hasHoInverse, fun h ↦ h.categoricalEquivalences⟩

/-- Let X,Y be quasicategories in universe u and f:X→Y have a reverse map with the two inverse
isomorphisms in ho(X^X),ho(Y^Y). There is g:Y→X and equivalence edges [f≫g]→[id_X] in X^X and
[g≫f]→[id_Y] in Y^Y, where brackets denote the vertices classified by those maps. -/
theorem HasHoInverse.exists_isEquivalence_edges [Quasicategory X]
    [Quasicategory Y] (h : HasHoInverse f) :
    ∃ g : Y ⟶ X,
      (∃ e : Edge (ihomVertexEquiv X X (f ≫ g)) (ihomVertexEquiv X X (𝟙 X)),
        e.IsEquivalence) ∧
      (∃ e : Edge (ihomVertexEquiv Y Y (g ≫ f)) (ihomVertexEquiv Y Y (𝟙 Y)),
        e.IsEquivalence) := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := h
  obtain ⟨eX, heX⟩ := Edge.exists_toHoHom_eq α.hom
  obtain ⟨eY, heY⟩ := Edge.exists_toHoHom_eq β.hom
  refine ⟨g, ⟨eX, ?_⟩, ⟨eY, ?_⟩⟩
  · rw [Edge.isEquivalence_iff, heX]
    infer_instance
  · rw [Edge.isEquivalence_iff, heY]
    infer_instance

/-!
## The induced homotopy-category equivalence

A categorical f:X→Y induces an equivalence ho(X)→ho(Y) for arbitrary X,Y. Every vertex y of Y is
isomorphic in ho(Y) to f(x) for some vertex x of X; when Y is a quasicategory this isomorphism
is represented by an equivalence edge f(x)→y.
-/

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. Then the induced functor
ho(f):ho(X)→ho(Y) is an equivalence of categories. The statement applies to arbitrary simplicial
X,Y. -/
theorem categoricalEquivalences.isEquivalence_mapHomotopyCategory
    (hf : categoricalEquivalences f) :
    (mapHomotopyCategory f).IsEquivalence := by
  have : (hoFunctor.map ((pre f).app
        (CategoryTheory.nerve X.HomotopyCategory))).toFunctor.IsEquivalence :=
    hf.hoPre_nerve_isEquivalence X.HomotopyCategory
  obtain ⟨a, ⟨α⟩⟩ := Functor.EssSurj.mem_essImage
    (hoFunctor.map ((pre f).app
      (CategoryTheory.nerve X.HomotopyCategory))).toFunctor
    (HomotopyCategory.mk (ihomVertexEquiv X _
      (CategoryTheory.nerveAdjunction.unit.app X :
        X ⟶ CategoryTheory.nerve X.HomotopyCategory)))
  obtain ⟨g, rfl⟩ := exists_eq_mk_ihomVertexEquiv a
  rw [hoPre_obj_mk_ihomVertexEquiv] at α
  have isoFG : mapHomotopyCategory f ⋙ descNerve g ≅
      𝟭 X.HomotopyCategory := by
    have h := (hoFunNerveComparison X X.HomotopyCategory).mapIso α
    rw [hoFunNerveComparison_obj_mk_ihomVertexEquiv (f ≫ g),
      hoFunNerveComparison_obj_mk_ihomVertexEquiv (Z := X)
        (D := X.HomotopyCategory)
        (CategoryTheory.nerveAdjunction.unit.app X),
      descNerve_precomp, descNerve_nerveAdjunction_unit_app] at h
    exact h
  have : (hoFunctor.map ((pre f).app
        (CategoryTheory.nerve Y.HomotopyCategory))).toFunctor.IsEquivalence :=
    hf.hoPre_nerve_isEquivalence Y.HomotopyCategory
  have hpost : (HomotopyCategory.mk (ihomVertexEquiv X _
        (f ≫ g ≫ CategoryTheory.nerveMap (mapHomotopyCategory f))) :
        hoFunctor.obj
          ((ihom X).obj (CategoryTheory.nerve Y.HomotopyCategory))) ≅
      HomotopyCategory.mk (ihomVertexEquiv X _
        (f ≫ (CategoryTheory.nerveAdjunction.unit.app Y :
          Y ⟶ CategoryTheory.nerve Y.HomotopyCategory))) := by
    have h := (hoFunctor.map ((ihom X).map
      (CategoryTheory.nerveMap (mapHomotopyCategory f)))).toFunctor.mapIso α
    have hnat : f ≫ (CategoryTheory.nerveAdjunction.unit.app Y :
          Y ⟶ CategoryTheory.nerve Y.HomotopyCategory) =
        (CategoryTheory.nerveAdjunction.unit.app X :
          X ⟶ CategoryTheory.nerve X.HomotopyCategory) ≫
          CategoryTheory.nerveMap (mapHomotopyCategory f) :=
      CategoryTheory.nerveAdjunction.unit.naturality f
    rw [hoPost_obj_mk_ihomVertexEquiv,
      hoPost_obj_mk_ihomVertexEquiv (A := X)
        (B := CategoryTheory.nerve X.HomotopyCategory)
        (C := CategoryTheory.nerve Y.HomotopyCategory)
        (CategoryTheory.nerveAdjunction.unit.app X)
        (CategoryTheory.nerveMap (mapHomotopyCategory f)),
      Category.assoc] at h
    exact h.trans (eqToIso (congrArg
      (fun m => HomotopyCategory.mk (ihomVertexEquiv X _ m))
      hnat.symm))
  have hpre : (hoFunctor.map ((pre f).app
        (CategoryTheory.nerve Y.HomotopyCategory))).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv Y _
          (g ≫ CategoryTheory.nerveMap (mapHomotopyCategory f)))) ≅
      (hoFunctor.map ((pre f).app
        (CategoryTheory.nerve Y.HomotopyCategory))).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv Y _
          (CategoryTheory.nerveAdjunction.unit.app Y :
            Y ⟶ CategoryTheory.nerve Y.HomotopyCategory))) := by
    rw [hoPre_obj_mk_ihomVertexEquiv,
      hoPre_obj_mk_ihomVertexEquiv (A := X) (B := Y)
        (C := CategoryTheory.nerve Y.HomotopyCategory) f
        (CategoryTheory.nerveAdjunction.unit.app Y)]
    exact hpost
  have isoGF : descNerve g ⋙ mapHomotopyCategory f ≅
      𝟭 Y.HomotopyCategory := by
    have β := (hoFunctor.map ((pre f).app
      (CategoryTheory.nerve Y.HomotopyCategory))).toFunctor.preimageIso hpre
    have h := (hoFunNerveComparison Y Y.HomotopyCategory).mapIso β
    rw [hoFunNerveComparison_obj_mk_ihomVertexEquiv
        (g ≫ CategoryTheory.nerveMap (mapHomotopyCategory f)),
      hoFunNerveComparison_obj_mk_ihomVertexEquiv (Z := Y)
        (D := Y.HomotopyCategory)
        (CategoryTheory.nerveAdjunction.unit.app Y),
      descNerve_postcomp_nerveMap, descNerve_nerveAdjunction_unit_app] at h
    exact h
  exact Functor.IsEquivalence.mk' (descNerve g) isoFG.symm isoGF

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. The functor assigned to
f by the homotopy-category construction ho is an equivalence ho(X)→ho(Y). -/
theorem categoricalEquivalences.isEquivalence_hoFunctor_map
    (hf : categoricalEquivalences f) :
    (hoFunctor.map f).toFunctor.IsEquivalence := by
  rw [show (hoFunctor.map f).toFunctor = mapHomotopyCategory f from rfl]
  exact hf.isEquivalence_mapHomotopyCategory

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. For every y∈Y₀ there is
x∈X₀ with an isomorphism [f(x)]≅[y] in ho(Y). -/
theorem categoricalEquivalences.exists_nonempty_iso_mk_app
    (hf : categoricalEquivalences f) (y : Y _⦋0⦌) :
    ∃ x : X _⦋0⦌, Nonempty
      (HomotopyCategory.mk (f.app (op ⦋0⦌) x) ≅ HomotopyCategory.mk y) := by
  have := hf.isEquivalence_mapHomotopyCategory
  obtain ⟨a, ⟨α⟩⟩ := Functor.EssSurj.mem_essImage (mapHomotopyCategory f)
    (HomotopyCategory.mk y)
  obtain ⟨x, rfl⟩ : ∃ x, HomotopyCategory.mk x = a :=
    ⟨_, HomotopyCategory.objEquiv.left_inv a⟩
  rw [mapHomotopyCategory_obj_mk] at α
  exact ⟨x, ⟨α⟩⟩

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. If Y is a quasicategory,
then for every y∈Y₀ there are x∈X₀ and an equivalence edge f(x)→y in Y. -/
theorem categoricalEquivalences.exists_isEquivalence_edge_app
    [Quasicategory Y] (hf : categoricalEquivalences f) (y : Y _⦋0⦌) :
    ∃ (x : X _⦋0⦌) (e : Edge (f.app (op ⦋0⦌) x) y), e.IsEquivalence := by
  obtain ⟨x, ⟨α⟩⟩ := hf.exists_nonempty_iso_mk_app y
  obtain ⟨e, he⟩ := Edge.exists_toHoHom_eq α.hom
  refine ⟨x, e, ?_⟩
  rw [Edge.isEquivalence_iff, he]
  infer_instance

/-!
## The Dwyer–Kan predicates

Essential surjectivity concerns ho(f), and full faithfulness concerns weak homotopy equivalences
of realized right mapping-space maps. Full faithfulness contains identities and is stable under
composition, and the conjunction with essential surjectivity is stable under composition.
-/

/-- For any f:X→Y of simplicial sets in universe u, define Dwyer–Kan essential surjectivity to mean
that ho(f):ho(X)→ho(Y) is essentially surjective: every object of ho(Y) is isomorphic to the
image of an object of ho(X). -/
def dwyerKanEssentiallySurjective (f : X ⟶ Y) : Prop :=
  (mapHomotopyCategory f).EssSurj

/-- For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. Define full faithfulness
to mean that |f_{a,b}| is a weak homotopy equivalence for every a,b:Δ[0]→X. This is a condition
on realized right mapping-space maps. -/
def dwyerKanFullyFaithful (f : X ⟶ Y) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
    realizationWeakEquivalences (mappingSpaceRight.map X a b f)

/-- For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. If f is fully faithful on
these mapping spaces, then for any x,y∈X₀ the map R_X(const_x,const_y)→R_Y(const_x≫f,const_y≫f)
is a realized weak homotopy equivalence. -/
theorem dwyerKanFullyFaithful.vertex (h : dwyerKanFullyFaithful f)
    (x y : X _⦋0⦌) :
    realizationWeakEquivalences
      (mappingSpaceRight.map X (const x) (const y) f) :=
  h (const x) (const y)

/-- For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. Suppose R_X(a,b) and
R_Y(a≫f,b≫f) are Kan for every a,b:Δ[0]→X, and every f_{a,b} is a simplicial weak equivalence.
Then f is Dwyer–Kan fully faithful. -/
theorem dwyerKanFullyFaithful.of_kanComplexW
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (hW : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex.W (mappingSpaceRight.map X a b f)) :
    dwyerKanFullyFaithful f := by
  intro a b
  have : KanComplex (mappingSpaceRight X a b) := hKanX a b
  have : KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)) :=
    hKanY a b
  exact (KanComplex.W_iff_realizationWeakEquivalence
    (mappingSpaceRight.map X a b f)).mp (hW a b)

/-- For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. Suppose f is Dwyer–Kan
fully faithful and both right mapping spaces are Kan for every a,b:Δ[0]→X. Then each f_{a,b} is
a simplicial weak equivalence. -/
theorem dwyerKanFullyFaithful.kanComplexW
    (h : dwyerKanFullyFaithful f)
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex.W (mappingSpaceRight.map X a b f) := by
  have : KanComplex (mappingSpaceRight X a b) := hKanX a b
  have : KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)) :=
    hKanY a b
  exact (KanComplex.W_iff_realizationWeakEquivalence
    (mappingSpaceRight.map X a b f)).mpr (h a b)

/-- For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. Define a Dwyer–Kan
equivalence by the conjunction that ho(f) is essentially surjective and each |f_{a,b}| is a weak
homotopy equivalence. -/
def isDwyerKanEquivalence (f : X ⟶ Y) : Prop :=
  dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithful f

/-- For f:X→Y in universe u, the Dwyer–Kan equivalence condition implies that ho(f):ho(X)→ho(Y) is
essentially surjective. -/
theorem isDwyerKanEquivalence.dwyerKanEssentiallySurjective
    (h : isDwyerKanEquivalence f) : dwyerKanEssentiallySurjective f :=
  h.1

/-- For f:X→Y in universe u, let R_X(a,b) be the right mapping-space model for vertex maps
a,b:Δ[0]→X, and f_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) its postcomposition map. The Dwyer–Kan equivalence
condition implies that every |f_{a,b}| is a weak homotopy equivalence. -/
theorem isDwyerKanEquivalence.dwyerKanFullyFaithful
    (h : isDwyerKanEquivalence f) : dwyerKanFullyFaithful f :=
  h.2

/-- For simplicial sets in universe u, call f:X→Y categorical when precomposition induces an
equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. Then ho(f):ho(X)→ho(Y)
is essentially surjective, so f satisfies Dwyer–Kan essential surjectivity. -/
theorem categoricalEquivalences.dwyerKanEssentiallySurjective
    (hf : categoricalEquivalences f) :
    dwyerKanEssentiallySurjective f := by
  have := hf.isEquivalence_mapHomotopyCategory
  change (mapHomotopyCategory f).EssSurj
  infer_instance

/-- For any simplicial set X in universe u, id_X is Dwyer–Kan fully faithful: every induced right
mapping-space map R_X(a,b)→R_X(a,b) is the identity, whose realization is a weak homotopy
equivalence. -/
theorem dwyerKanFullyFaithful_id :
    dwyerKanFullyFaithful (𝟙 X) := by
  intro a b
  rw [mappingSpaceRight.map_id]
  exact realizationWeakEquivalences.id_mem _

/-- For f:X→Y and g:Y→Z in universe u, if each induced right mapping-space map of f and of g is a
realized weak homotopy equivalence, then the same holds for f≫g. Thus Dwyer–Kan full
faithfulness is closed under composition. -/
theorem dwyerKanFullyFaithful.comp {g : Y ⟶ Z}
    (hf : dwyerKanFullyFaithful f) (hg : dwyerKanFullyFaithful g) :
    dwyerKanFullyFaithful (f ≫ g) := by
  intro a b
  rw [mappingSpaceRight.map_comp]
  exact realizationWeakEquivalences.comp_mem _ _ (hf a b)
    (hg (a ≫ f) (b ≫ f))

/-- For f:X→Y and g:Y→Z in universe u, if both are Dwyer–Kan equivalences—essentially surjective on
homotopy categories and fully faithful on realized right mapping spaces—then f≫g is a Dwyer–Kan
equivalence. -/
theorem isDwyerKanEquivalence.comp {g : Y ⟶ Z}
    (hf : isDwyerKanEquivalence f) (hg : isDwyerKanEquivalence g) :
    isDwyerKanEquivalence (f ≫ g) := by
  refine ⟨?_, hf.dwyerKanFullyFaithful.comp hg.dwyerKanFullyFaithful⟩
  have hcomp : mapHomotopyCategory (f ≫ g) =
      mapHomotopyCategory f ⋙ mapHomotopyCategory g := by
    have hrw : ∀ {A B : SSet.{u}} (h : A ⟶ B),
        mapHomotopyCategory h = (hoFunctor.map h).toFunctor := fun _ ↦ rfl
    rw [hrw, hrw, hrw, hoFunctor.map_comp]
    rfl
  change (mapHomotopyCategory (f ≫ g)).EssSurj
  rw [hcomp]
  have : (mapHomotopyCategory f).EssSurj :=
    hf.dwyerKanEssentiallySurjective
  have : (mapHomotopyCategory g).EssSurj :=
    hg.dwyerKanEssentiallySurjective
  infer_instance

end SSet

end
