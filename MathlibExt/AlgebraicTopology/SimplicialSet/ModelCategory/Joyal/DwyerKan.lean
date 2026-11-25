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
# Dwyer–Kan predicates and categorical equivalences

The public predicates `SSet.dwyerKanEssentiallySurjective`,
`SSet.dwyerKanFullyFaithful`, and `SSet.isDwyerKanEquivalence` retain
ordinary homotopy-category essential surjectivity and weak equivalences
of the actual right mapping-space maps. They apply to arbitrary simplicial
sets; Kan hypotheses are needed only for the `SSet.KanComplex.W` bridge.

This foundational module proves homotopy inverses for categorical
equivalences between quasicategories, equivalence on ordinary homotopy
categories, essential surjectivity, and identity and composition laws.

The complete recognition theorem is proved in `DwyerKanRecognition.lean`
and reexported by `DwyerKanFinal.lean`:
`SSet.categoricalEquivalences_iff_isDwyerKanEquivalence`. For original
quasicategories it includes both categorical-to-mapping-space weakness
and the Dwyer–Kan converse. The proof uses the genuine pointed Joyal
model, Brown factorization, and full boundary lifting. The foundational
import direction here keeps these predicates available to that proof.

## References

- D. Stevenson, *Notes on the Joyal model structure*,
  [arXiv:1810.05233v1](https://arxiv.org/abs/1810.05233v1), §2.4,
  Definition 2.16 and Proposition 2.24 (printed page 9). The source uses
  left mapping spaces; the formal predicates use right mapping spaces.
- J. Lurie, *Higher Topos Theory*, §1.2.2 for mapping-space models.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}

/-!
## Vertex-level formulas for pre/postcomposition on `h Fun`
-/

/-- Every object of `h Fun(Z, C)` is the vertex classified by a map
`Z ⟶ C`. -/
private lemma exists_eq_mk_ihomVertexEquiv {Z C : SSet.{u}}
    (a : ((ihom Z).obj C).HomotopyCategory) :
    ∃ m : Z ⟶ C, a = HomotopyCategory.mk (ihomVertexEquiv Z C m) := by
  refine ⟨(ihomVertexEquiv Z C).symm (HomotopyCategory.objEquiv a), ?_⟩
  rw [Equiv.apply_symm_apply]
  exact (HomotopyCategory.objEquiv.left_inv a).symm

/-- Precomposition on `h Fun` sends the vertex classified by `m` to the
vertex classified by `f ≫ m`. -/
private lemma hoPre_obj_mk_ihomVertexEquiv {A B C : SSet.{u}} (f : A ⟶ B)
    (m : B ⟶ C) :
    (hoFunctor.map ((pre f).app C)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv B C m)) =
      HomotopyCategory.mk (ihomVertexEquiv A C (f ≫ m)) := by
  change (mapHomotopyCategory ((pre f).app C)).obj _ = _
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_pre_app]

/-- Postcomposition on `h Fun` sends the vertex classified by `m` to
the vertex classified by `m ≫ q`. -/
private lemma hoPost_obj_mk_ihomVertexEquiv {A B C : SSet.{u}} (m : A ⟶ B)
    (q : B ⟶ C) :
    (hoFunctor.map ((ihom A).map q)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv A B m)) =
      HomotopyCategory.mk (ihomVertexEquiv A C (m ≫ q)) := by
  change (mapHomotopyCategory ((ihom A).map q)).obj _ = _
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_ihom_map]

/-!
## Equivalences in the sense of Stevenson Definition 2.1 (`h`-form)
-/

/-- A map with a homotopy inverse is a categorical equivalence; this
is `SSet.categoricalEquivalences.of_hoCompIso`, restated through
`SSet.HasHoInverse`. -/
theorem HasHoInverse.categoricalEquivalences (h : HasHoInverse f) :
    categoricalEquivalences f := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := h
  exact categoricalEquivalences.of_hoCompIso g α β

/-- For a map between quasicategories, being a categorical
equivalence is the same as being an equivalence in the sense of
Stevenson Definition 2.1, read in homotopy categories of functor
objects. -/
theorem categoricalEquivalences_iff_hasHoInverse [Quasicategory X]
    [Quasicategory Y] :
    categoricalEquivalences f ↔ HasHoInverse f :=
  ⟨fun hf ↦ hf.hasHoInverse, fun h ↦ h.categoricalEquivalences⟩

/-- The edge form of `SSet.categoricalEquivalences.hasHoInverse`:
the homotopy inverse of a categorical equivalence between
quasicategories can be witnessed by equivalence edges of the functor
quasicategories, i.e. Stevenson Definition 2.1 on the nose. -/
theorem HasHoInverse.exists_isEquivalence_edges [Quasicategory X]
    [Quasicategory Y] (h : HasHoInverse f) :
    ∃ g : Y ⟶ X,
      (∃ e : Edge (ihomVertexEquiv X X (f ≫ g)) (ihomVertexEquiv X X (𝟙 X)),
        e.IsEquivalence) ∧
      (∃ e : Edge (ihomVertexEquiv Y Y (g ≫ f)) (ihomVertexEquiv Y Y (𝟙 Y)),
        e.IsEquivalence) := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := h
  obtain ⟨eX, heX⟩ := Edge.exists_homMk_eq α.hom
  obtain ⟨eY, heY⟩ := Edge.exists_homMk_eq β.hom
  refine ⟨g, ⟨eX, ?_⟩, ⟨eY, ?_⟩⟩
  · rw [Edge.isEquivalence_iff, heX]
    infer_instance
  · rw [Edge.isEquivalence_iff, heY]
    infer_instance

/-!
## Categorical equivalences induce equivalences on homotopy categories
-/

/-- **A categorical equivalence induces an equivalence of ordinary
homotopy categories** using the ordinary nerve comparison functor. No quasicategory hypothesis on
source or target is needed: test against the nerves
`nerve X.HomotopyCategory` and `nerve Y.HomotopyCategory`.
Essential surjectivity at the vertex of `CategoryTheory.nerveAdjunction.unit.app X` gives
`g : Y ⟶ nerve X.HomotopyCategory`; the object formula
`SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv` turns the
resulting isomorphism into `mapHomotopyCategory f ⋙ descNerve g ≅ 𝟭`,
and postcomposing with `nerveMap (mapHomotopyCategory f)`,
transporting along `CategoryTheory.nerveAdjunction.unit.naturality`, and reflecting
along the equivalence at `nerve Y.HomotopyCategory`
(`Functor.preimageIso`) gives the other triangle
`descNerve g ⋙ mapHomotopyCategory f ≅ 𝟭`. -/
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

/-- The `hoFunctor` form of
`SSet.categoricalEquivalences.isEquivalence_mapHomotopyCategory`. -/
theorem categoricalEquivalences.isEquivalence_hoFunctor_map
    (hf : categoricalEquivalences f) :
    (hoFunctor.map f).toFunctor.IsEquivalence := by
  rw [show (hoFunctor.map f).toFunctor = mapHomotopyCategory f from rfl]
  exact hf.isEquivalence_mapHomotopyCategory

/-- **Essential surjectivity on vertices** for a categorical
equivalence: every vertex of `Y` is isomorphic in `Y.HomotopyCategory`
to the image of a vertex of `X`. This is Stevenson
Definition 2.16(i) at the vertex level. -/
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

/-- **Essential surjectivity up to equivalence edge** for a categorical
equivalence into a quasicategory: every vertex of `Y` receives an
equivalence edge from the image of a vertex of `X`. -/
theorem categoricalEquivalences.exists_isEquivalence_edge_app
    [Quasicategory Y] (hf : categoricalEquivalences f) (y : Y _⦋0⦌) :
    ∃ (x : X _⦋0⦌) (e : Edge (f.app (op ⦋0⦌) x) y), e.IsEquivalence := by
  obtain ⟨x, ⟨α⟩⟩ := hf.exists_nonempty_iso_mk_app y
  obtain ⟨e, he⟩ := Edge.exists_homMk_eq α.hom
  refine ⟨x, e, ?_⟩
  rw [Edge.isEquivalence_iff, he]
  infer_instance

/-!
## Dwyer–Kan equivalences (Stevenson Definition 2.16)
-/

/-- Stevenson Definition 2.16(i): a map of simplicial sets is
*essentially surjective* if the induced functor on homotopy
categories is essentially surjective. -/
def dwyerKanEssentiallySurjective (f : X ⟶ Y) : Prop :=
  (mapHomotopyCategory f).EssSurj

/-- The fully-faithful half of Stevenson Definition 2.16(ii), stated
with the join-slice *right* mapping spaces of `JoinSlice.lean`
(Stevenson uses left mapping spaces; see the references above): for all vertex
maps `a b : Δ[0] ⟶ X`, the induced map
`mappingSpaceRight X a b ⟶ mappingSpaceRight Y (a ≫ f) (b ≫ f)`
given by postcomposition (`SSet.mappingSpaceRight.map`) is a
realization weak equivalence (`SSet.realizationWeakEquivalences`,
the weak equivalences of the Quillen model structure on simplicial
sets). For element vertices `x : X _⦋0⦌` the vertex map is
`SSet.const x` and its image is the vertex map of the image vertex,
since `const x ≫ f = const (f.app _ x)` by `SSet.const_comp`; see
`SSet.dwyerKanFullyFaithful.vertex`. Note
`SSet.realizationWeakEquivalences` is defined on arbitrary
simplicial sets and imposes no Kan hypothesis on the mapping
spaces; when the mapping spaces are Kan complexes it agrees with
`SSet.KanComplex.W` by
`SSet.KanComplex.W_iff_realizationWeakEquivalence` (see
`SSet.dwyerKanFullyFaithful.of_kanComplexW` and
`SSet.dwyerKanFullyFaithful.kanComplexW`). -/
def dwyerKanFullyFaithful (f : X ⟶ Y) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
    realizationWeakEquivalences (mappingSpaceRight.map X a b f)

/-- The vertex form of `SSet.dwyerKanFullyFaithful`: for vertices
`x y : X _⦋0⦌`, the induced map on right mapping spaces between
the vertex maps `const x`, `const y` and their images
`const x ≫ f = const (f.app _ x)`, `const y ≫ f` is a realization
weak equivalence. -/
theorem dwyerKanFullyFaithful.vertex (h : dwyerKanFullyFaithful f)
    (x y : X _⦋0⦌) :
    realizationWeakEquivalences
      (mappingSpaceRight.map X (const x) (const y) f) :=
  h (const x) (const y)

/-- Bridge from `SSet.KanComplex.W` to full faithfulness: if all
source right mapping spaces and all target right mapping spaces at
`f`-image vertices are Kan complexes, and every induced map on
right mapping spaces is a `SSet.KanComplex.W` weak equivalence,
then `f` is fully faithful on mapping spaces. This is
`SSet.KanComplex.W_iff_realizationWeakEquivalence` applied
pointwise, with the `SSet.KanComplex` instances supplied from
`hKanX` and `hKanY`. -/
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

/-- Bridge from full faithfulness to `SSet.KanComplex.W`: if `f`
is fully faithful on mapping spaces and all source right mapping
spaces and all target right mapping spaces at `f`-image vertices
are Kan complexes, then every induced map on right mapping spaces
is a `SSet.KanComplex.W` weak equivalence. This is
`SSet.KanComplex.W_iff_realizationWeakEquivalence` applied
pointwise, with the `SSet.KanComplex` instances supplied from
`hKanX` and `hKanY`. -/
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

/-- Stevenson Definition 2.16: a map is a *Dwyer–Kan equivalence* if
it is essentially surjective (`SSet.dwyerKanEssentiallySurjective`)
and fully faithful on mapping spaces
(`SSet.dwyerKanFullyFaithful`). No quasicategory hypothesis is
built into the predicate; Stevenson states it for maps between
`∞`-categories, and Remark 2.18 extends it to general maps. -/
def isDwyerKanEquivalence (f : X ⟶ Y) : Prop :=
  dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithful f

/-- A Dwyer–Kan equivalence is essentially surjective. -/
theorem isDwyerKanEquivalence.dwyerKanEssentiallySurjective
    (h : isDwyerKanEquivalence f) : dwyerKanEssentiallySurjective f :=
  h.1

/-- A Dwyer–Kan equivalence is fully faithful on mapping spaces. -/
theorem isDwyerKanEquivalence.dwyerKanFullyFaithful
    (h : isDwyerKanEquivalence f) : dwyerKanFullyFaithful f :=
  h.2

/-- **A categorical equivalence is essentially surjective** in the
sense of Stevenson Definition 2.16(i): this is the
essentially-surjective half of "categorical ⇒ Dwyer–Kan". -/
theorem categoricalEquivalences.dwyerKanEssentiallySurjective
    (hf : categoricalEquivalences f) :
    dwyerKanEssentiallySurjective f := by
  have := hf.isEquivalence_mapHomotopyCategory
  change (mapHomotopyCategory f).EssSurj
  infer_instance

/-- The identity map is fully faithful on mapping spaces for
every simplicial set: the induced map is the identity
(`SSet.mappingSpaceRight.map_id`), a realization weak equivalence
by `SSet.realizationWeakEquivalences.id_mem` (realization weak
equivalences contain identities on arbitrary simplicial sets; no
Kan hypothesis on the mapping spaces is needed). -/
theorem dwyerKanFullyFaithful_id :
    dwyerKanFullyFaithful (𝟙 X) := by
  intro a b
  rw [mappingSpaceRight.map_id]
  exact realizationWeakEquivalences.id_mem _

/-- Full faithfulness on mapping spaces is stable under
composition, by `SSet.mappingSpaceRight.map_comp` and
`SSet.realizationWeakEquivalences.comp_mem` (realization weak
equivalences are stable under composition). -/
theorem dwyerKanFullyFaithful.comp {g : Y ⟶ Z}
    (hf : dwyerKanFullyFaithful f) (hg : dwyerKanFullyFaithful g) :
    dwyerKanFullyFaithful (f ≫ g) := by
  intro a b
  rw [mappingSpaceRight.map_comp]
  exact realizationWeakEquivalences.comp_mem _ _ (hf a b)
    (hg (a ≫ f) (b ≫ f))

/-- Dwyer–Kan equivalences are stable under composition: essential
surjectivity composes (using functoriality of
`SSet.mapHomotopyCategory` through `SSet.hoFunctor.map_comp`), and
full faithfulness composes by
`SSet.dwyerKanFullyFaithful.comp`. -/
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
