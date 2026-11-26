/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldFiniteGaloisNeighborhoods
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricStalkExactness
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Finite Galois section colimits and geometric stalks

Let k,Ω be fields of universe u with Ω a prescribed separable closure. The functor from finite
Galois subfields L⊆Ω to opposite pointed étale neighborhoods is fully faithful and final.
Raising the geometric fiber to height max(u,w) lifts only its pointing coordinates and
preserves the underlying étale objects and arrows.

For an additive-group sheaf Q of that height, the directed diagram L ↦ Q(Spec L), with
restriction maps for L⊆M, has a colimit canonically isomorphic to the geometric stalk at
Spec(Ω). Stage inclusions correspond to germs, naturally in Q. If Q begins with smaller
coefficients of universe w, applying ULift^u once gives the same formulas on lifted sections.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let k,Ω be fields with Ω a prescribed separable closure. The functor from finite Galois
intermediate fields to opposite geometric neighborhoods is full: every pointed spectrum
morphism between its values is induced by an inclusion of the same subfields. Its underlying
spectrum map respects the inclusions into Ω. -/
instance fieldFiniteGaloisNeighborhoodFunctor_full :
    (fieldFiniteGaloisNeighborhoodFunctor k Ω).Full where
  map_surjective {L M} a := by
    let r : Spec (.of M) ⟶ Spec (.of L) := a.unop.hom.left
    have hr : r ≫ Spec.algebraMap k L = Spec.algebraMap k M :=
      MorphismProperty.Over.w a.unop.hom
    let μ : L →ₐ[k] M := Spec.homEquivAlgHom ⟨r, hr⟩
    have hμ : Spec.map (CommRingCat.ofHom μ.toRingHom) = r := by
      change Spec.map (Spec.preimage r) = r
      exact Spec.map_preimage r
    have hz : Spec.algebraMap M Ω ≫ r = Spec.algebraMap L Ω :=
      congrArg (fun z => z.left) a.unop.map_val
    have hring : CommRingCat.ofHom μ.toRingHom ≫
        CommRingCat.ofHom (algebraMap M Ω) = CommRingCat.ofHom (algebraMap L Ω) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hμ]
      exact hz
    have hval (x : L) : (μ x : Ω) = (x : Ω) := by
      exact congrArg
        (fun f : CommRingCat.of L ⟶ CommRingCat.of Ω => f.hom x) hring
    have hLM : L ≤ M := by
      intro x hx
      have h := hval (⟨x, hx⟩ : L)
      change (μ (⟨x, hx⟩ : L)).val = x at h
      exact h ▸ (μ (⟨x, hx⟩ : L)).property
    have hinc : μ = IntermediateField.inclusion hLM := by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      exact hval x
    refine ⟨homOfLE hLM, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hLM).toRingHom) = r
    rw [← hinc]
    exact hμ

/-- For a field k and prescribed separable closure Ω, the finite Galois neighborhood functor into
the opposite geometric-neighborhood category is final. Every pointed étale neighborhood has a
finite Galois refinement, and the filtered-neighborhood and full-faithful properties give the
connectedness required for colimit comparison. -/
instance fieldFiniteGaloisNeighborhoodFunctor_final :
    (fieldFiniteGaloisNeighborhoodFunctor k Ω).Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful
    (fieldFiniteGaloisNeighborhoodFunctor k Ω)
    (fieldFiniteGaloisNeighborhoodFunctor_refines k Ω)

/-- Let k,Ω be fields in universe u with Ω a separable closure. The geometric-neighborhood
category is equivalent to the category of elements of the common-height geometric fiber at
max(u,w). The forward functor keeps the étale object and replaces its pointing z by up(z). -/
abbrev fieldGeometricElementsLiftEquivalence :
    FieldGeometricNeighborhoods k Ω ≌
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.Elements :=
  smallEtaleGeometricElementsLiftEquivalence.{u, w} (Spec.algebraMap k Ω)

/-- For a prescribed geometric point of Spec(k), a neighborhood a=(U,z) is sent by
fieldGeometricElementsLiftEquivalence to (U,up(z)). The lift raises the fiber index to the
coefficient working height max(u,w), while the étale object remains U. -/
theorem fieldGeometricElementsLiftEquivalence_obj (a : FieldGeometricNeighborhoods k Ω) :
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.obj a =
      Functor.elementsMk _ a.obj (ULift.up a.val) := rfl

/-- Let Ω be a prescribed separable closure of k. Composing the forward point-index lift
equivalence with the category-of-elements projection to the small étale category equals the
projection from the unlifted neighborhood category. This is equality of functors on both
objects and étale morphisms. -/
theorem fieldGeometricElementsLiftEquivalence_comp_projection :
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor ⋙
        Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber =
      Functor.Elements.π (fieldGeometricPoint k Ω).fiber := rfl

/-- For k and a prescribed separable closure Ω, compose the finite Galois neighborhood functor
with the opposite of the point-index lift equivalence. This gives a functor into the opposite
common-height neighborhood category, preserving Spec(L) and lifting its geometric pointing. -/
abbrev fieldFiniteGaloisCommonNeighborhoodFunctor :=
  fieldFiniteGaloisNeighborhoodFunctor k Ω ⋙
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.op

instance fieldFiniteGaloisCommonNeighborhoodFunctor_final :
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).Final := by
  infer_instance

/-- Let Ω be a prescribed separable closure of k. Project the common-height finite Galois
neighborhood functor to the opposite small étale category. It sends L to Spec(L) and an
inclusion L⊆M to the presheaf-direction arrow corresponding to Spec(M) → Spec(L). -/
abbrev fieldFiniteGaloisSectionsIndex :=
  fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω ⋙
    (Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op

theorem fieldFiniteGaloisSectionsIndex_original :
    fieldFiniteGaloisSectionsIndex.{u, w} k Ω =
      fieldFiniteGaloisNeighborhoodFunctor k Ω ⋙
        (Functor.Elements.π (fieldGeometricPoint k Ω).fiber).op := rfl

/-- For a small-étale additive-group sheaf Q on Spec(k) of universe max(u,w), define the diagram
on finite Galois subfields L⊆Ω by L ↦ Q(Spec L). Its map for L⊆M is the restriction Q(Spec L)
→ Q(Spec M) along the subfield spectrum arrow. -/
abbrev fieldFiniteGaloisSectionDiagram
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  fieldFiniteGaloisSectionsIndex.{u, w} k Ω ⋙ Q.obj

theorem fieldFiniteGaloisSectionDiagram_obj
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).obj L =
      Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L)) := rfl

theorem fieldFiniteGaloisSectionDiagram_map
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    {L M : FiniteGaloisIntermediateField k Ω} (f : L ⟶ M) :
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).map f =
      Q.obj.map (fieldFiniteGaloisInclusion k Ω (leOfHom f)).op := rfl

/-- Let Ω be a prescribed separable closure of k and Q an additive-group small-étale sheaf of
height max(u,w). The diagram L ↦ Q(Spec L) over finite Galois intermediate fields has a
colimit. Existence follows by finality from the geometric stalk colimit, for this specified
sheaf diagram. -/
instance fieldFiniteGaloisSectionDiagram_hasColimit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    HasColimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :=
  Functor.Final.comp_hasColimit
    (G := (Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj)
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)

/-- For a field k, prescribed separable closure Ω, and additive-group small-étale sheaf Q of
height max(u,w), finality gives colim_{L⊆Ω finite Galois} Q(Spec L) ≅ Q_{arη}. The stalk is
the common-height geometric stalk of Spec(Ω) → Spec(k), and the comparison uses the same
section restrictions. -/
def fieldFiniteGaloisStalkIso
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) ≅
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q :=
  Functor.Final.colimitIso
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)
    ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj)

/-- Let Q be an additive-group sheaf on the small étale site of Spec(k), Ω a prescribed separable
closure, and L a finite Galois subfield. The stage map Q(Spec L) → colim_L Q(Spec L) followed
by fieldFiniteGaloisStalkIso equals the germ map at the inclusion Spec(Ω) → Spec(L), with its
pointing lifted to the common height. -/
@[reassoc]
theorem fieldFiniteGaloisStalkIso_ι_hom
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω) :
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L ≫
        (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).hom =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj :=
  Functor.Final.ι_colimitIso_hom
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)
    ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj) L

/-- Let k be a field, Ω a prescribed separable closure, Q an additive-group small-étale sheaf of
height max(u,w), and L a finite Galois subfield. The germ map Q(Spec L) → Q_{arη}, at the
lift Spec(Ω) → Spec(L), followed by the inverse finite Galois stalk isomorphism equals the
section-stage inclusion into colim_L Q(Spec L). -/
@[reassoc]
theorem fieldFiniteGaloisStalkIso_germ_inv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj ≫
        (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).inv =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L :=
  Functor.Final.ι_colimitIso_inv
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)
    ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj) L

/-- Let k have a prescribed separable closure Ω and τ : Q → Q′ be a small-étale additive-group
sheaf morphism of height max(u,w). Its section components τ_{Spec L} form a natural
transformation of the finite Galois diagrams, whose induced colimit map is
fieldFiniteGaloisStalkColimitMap(τ). -/
def fieldFiniteGaloisStalkColimitMap
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) ⟶
      colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q') :=
  colimMap (Functor.whiskerLeft (fieldFiniteGaloisSectionsIndex.{u, w} k Ω) τ.hom)

/-- For k and prescribed separable closure Ω, the assignment Q ↦ colim_L Q(Spec L) defines a
functor from small-étale additive-group sheaves of height max(u,w) to AddCommGrpCat of that
height. Its maps are induced by the sectionwise sheaf-morphism components. -/
def fieldFiniteGaloisStalkColimit :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      AddCommGrpCat.{max u w} where
  obj Q := colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q)
  map τ := fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ
  map_id Q := by
    apply colimit.hom_ext
    intro L
    simp [fieldFiniteGaloisStalkColimitMap]
  map_comp τ σ := by
    apply colimit.hom_ext
    intro L
    simp [fieldFiniteGaloisStalkColimitMap, Category.assoc]

/-- Let Ω be a prescribed separable closure of k, τ : Q → Q′ a small-étale additive-group sheaf
map, and e_Q,e_Q′ the finite Galois section-colimit isomorphisms. Then
colim(τ)≫e_Q′.hom=e_Q.hom≫τ_{arη}. This is an equality of additive-group maps from the
section colimit to the geometric stalk. -/
theorem fieldFiniteGaloisStalkIso_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ ≫
        (fieldFiniteGaloisStalkIso.{u, w} k Ω Q').hom =
      (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).hom ≫
        (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ := by
  apply colimit.hom_ext
  intro L
  rw [← Category.assoc, fieldFiniteGaloisStalkColimitMap, ι_colimMap]
  rw [Category.assoc, fieldFiniteGaloisStalkIso_ι_hom]
  rw [← Category.assoc, fieldFiniteGaloisStalkIso_ι_hom]
  exact ((smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).toPresheafFiber_naturality τ.hom _ _).symm

/-- For k,Ω with IsSepClosure k Ω, the functor taking additive-group sheaves of height max(u,w) to
their finite Galois section colimit is naturally isomorphic to the common geometric stalk
functor. Its component at Q is fieldFiniteGaloisStalkIso(Q). -/
def fieldFiniteGaloisStalkNatIso :
    fieldFiniteGaloisStalkColimit.{u, w} k Ω ≅
      smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) :=
  NatIso.ofComponents (fieldFiniteGaloisStalkIso.{u, w} k Ω)
    (fieldFiniteGaloisStalkIso_naturality.{u, w} k Ω)

/-- For a small-étale additive-group sheaf F of coefficient universe w, lift its coefficients by
ULift^u to height max(u,w). If c∈F(Spec L) for a finite Galois subfield L⊆Ω, the
colimit-to-stalk comparison sends the stage element up(c) to its geometric germ in the lifted
sheaf at the inclusion point Spec(Ω) → Spec(L). -/
theorem fieldFiniteGaloisStalkIso_original_section
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (L : FiniteGaloisIntermediateField k Ω)
    (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    (fieldFiniteGaloisStalkIso.{u, w} k Ω
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom
      (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) L (ULift.up c)) =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) :=
  ConcreteCategory.congr_hom
    (fieldFiniteGaloisStalkIso_ι_hom.{u, w} k Ω
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F) L) (ULift.up c)

/-- Let Ω be a prescribed separable closure of k, f : F → F′ a small-étale sheaf map with
coefficient universe w, and Lc the ULift^u coefficient functor. For the finite Galois colimit
maps C and stalk maps S, C(Lc(f))≫e_{Lc(F′)}=e_{Lc(F)}≫S(Lc(f)). The same natural comparison
is used at height max(u,w). -/
theorem fieldFiniteGaloisStalkIso_original_naturality
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    fieldFiniteGaloisStalkColimitMap.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
      (fieldFiniteGaloisStalkIso.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F')).hom =
    (fieldFiniteGaloisStalkIso.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom ≫
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) :=
  fieldFiniteGaloisStalkIso_naturality.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).map f)

/-- For k,Ω with IsSepClosure k Ω and a neighborhood morphism f : a → b, the forward map of
fieldGeometricElementsLiftEquivalence has underlying étale arrow f.hom. Only the pointing
coordinates are lifted; the site arrow itself is unchanged. -/
theorem fieldGeometricElementsLiftEquivalence_map
    {a b : FieldGeometricNeighborhoods k Ω} (f : a ⟶ b) :
    ((fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.map f).hom = f.hom := rfl

/-- Let Ω be a prescribed separable closure of k and L a finite Galois subfield. The common-height
neighborhood functor takes L to the opposite of (Spec(L),up(z_L)), where z_L is the geometric
lift induced by L⊆Ω. The étale object is the same spectrum over k. -/
theorem fieldFiniteGaloisCommonNeighborhoodFunctor_obj
    (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).obj L =
      op (Functor.elementsMk
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))) := rfl

/-- For finite Galois subfields L≤M inside a prescribed separable closure Ω, the common-height
functor map has underlying reverse neighborhood arrow Spec(M) → Spec(L), exactly
fieldFiniteGaloisInclusion(L≤M). Point-index lifting does not modify this arrow. -/
theorem fieldFiniteGaloisCommonNeighborhoodFunctor_map
    {L M : FiniteGaloisIntermediateField k Ω} (f : L ⟶ M) :
    ((fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).map f).unop.hom =
      fieldFiniteGaloisInclusion k Ω (leOfHom f) := rfl

/-- For a field k, prescribed separable closure Ω, and small-étale additive-group sheaf Q of
height max(u,w), the categorical stalk isomorphism gives an additive equivalence between the
section colimit colim_L Q(Spec L) and the common geometric stalk Q_{arη}. -/
def fieldFiniteGaloisStalkAddEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :
      AddCommGrpCat.{max u w}) ≃+
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q :=
  (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).addCommGroupIsoToAddEquiv

/-- Let Ω be a prescribed separable closure of k, Q a small-étale additive-group sheaf, L a finite
Galois subfield, and c∈Q(Spec L). The additive equivalence sends the colimit class ι_L(c) to
the germ of c at the inclusion Spec(Ω) → Spec(L), with the common-height pointing. -/
theorem fieldFiniteGaloisStalkAddEquiv_ι
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω)
    (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
      (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkIso_ι_hom.{u, w} k Ω Q L) c

/-- For k,Ω as a field and its prescribed separable closure, Q a small-étale additive-group sheaf,
and c∈Q(Spec L), the inverse additive stalk equivalence sends the geometric germ of c to
ι_L(c) in the finite Galois section colimit. -/
theorem fieldFiniteGaloisStalkAddEquiv_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω)
    (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q).symm
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c) =
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkIso_germ_inv.{u, w} k Ω Q L) c

/-- Let Ω be a prescribed separable closure of k, τ : Q → Q′ a small-étale sheaf map, and L a
finite Galois subfield. The section-colimit map satisfies ι_L^Q≫C(τ)=τ_{Spec L}≫ι_L^{Q′}. Thus
every stage map is the specified sheaf-morphism component. -/
@[reassoc]
theorem fieldFiniteGaloisStalkColimitMap_ι
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (L : FiniteGaloisIntermediateField k Ω) :
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L ≫
        fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ =
      τ.hom.app (op (fieldFiniteGaloisEtale k Ω L)) ≫
        colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q') L :=
  ι_colimMap (Functor.whiskerLeft (fieldFiniteGaloisSectionsIndex.{u, w} k Ω) τ.hom) L

/-- For a field k, prescribed separable closure Ω, and a sheaf morphism τ : Q → Q′, let C(τ) be
its finite Galois colimit map and S(τ) its stalk map. For any colimit element c,
e_{Q′}(C(τ)(c))=S(τ)(e_Q(c)), where e is the additive colimit-to-stalk equivalence. -/
theorem fieldFiniteGaloisStalkAddEquiv_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (c : (colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :
      AddCommGrpCat.{max u w})) :
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q'
        (fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ c) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ
        (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q c) :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkIso_naturality.{u, w} k Ω τ) c

/-- Let Ω be a prescribed separable closure of k, f : F → F′ a small-étale sheaf map of
coefficient universe w, and c∈F(Spec L). After the single ULift^u coefficient lift, the
induced colimit map sends ι_L(up(c)) to ι_L′(up(f_{Spec L}(c))). -/
theorem fieldFiniteGaloisStalkColimitMap_original_ι
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F')
    (L : FiniteGaloisIntermediateField k Ω)
    (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    fieldFiniteGaloisStalkColimitMap.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).map f)
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) L (ULift.up c)) =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F')) L
        (ULift.up (f.hom.app (op (fieldFiniteGaloisEtale k Ω L)) c)) :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkColimitMap_ι.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).map f) L) (ULift.up c)

/-- Let k have universe u and Ω be its prescribed separable closure. This proposition asserts that
the finite Galois neighborhood functor is full, faithful, and final; the point-index lift
takes (U,z) to (U,up(z)) and keeps its arrows; the common-height subfield functor is final
with those same lifted spectra and inclusion arrows; forgetting its pointing equals the
unlifted section-index functor; and for every small-étale sheaf Q of coefficient height
max(u,w), the diagram has a colimit, object Q(Spec L), and restriction map Q(Spec L) → Q(Spec
M) for L≤M. -/
def FieldFiniteGaloisColimitLaws : Prop :=
  (fieldFiniteGaloisNeighborhoodFunctor k Ω).Full ∧
  (fieldFiniteGaloisNeighborhoodFunctor k Ω).Faithful ∧
  (fieldFiniteGaloisNeighborhoodFunctor k Ω).Final ∧
  (∀ a : FieldGeometricNeighborhoods k Ω,
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.obj a =
      Functor.elementsMk _ a.obj (ULift.up a.val)) ∧
  (∀ (a b : FieldGeometricNeighborhoods k Ω) (f : a ⟶ b),
    ((fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.map f).hom = f.hom) ∧
  (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).Final ∧
  (∀ L : FiniteGaloisIntermediateField k Ω,
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).obj L =
      op (Functor.elementsMk
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)))) ∧
  (∀ (L M : FiniteGaloisIntermediateField k Ω) (f : L ⟶ M),
    ((fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).map f).unop.hom =
      fieldFiniteGaloisInclusion k Ω (leOfHom f)) ∧
  fieldFiniteGaloisSectionsIndex.{u, w} k Ω =
    fieldFiniteGaloisNeighborhoodFunctor k Ω ⋙
      (Functor.Elements.π (fieldGeometricPoint k Ω).fiber).op ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    HasColimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q)) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L : FiniteGaloisIntermediateField k Ω),
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).obj L =
      Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) ∧
  ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L M : FiniteGaloisIntermediateField k Ω) (f : L ⟶ M),
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).map f =
      Q.obj.map (fieldFiniteGaloisInclusion k Ω (leOfHom f)).op

/-- For a field k and prescribed separable closure Ω, let C be the finite Galois section-colimit
functor, S the common geometric stalk, e their natural isomorphism, and Lc the ULift^u
coefficient functor. This proposition asserts that e has the specified stalk-isomorphism
components; C preserves identities and composition; its additive equivalence sends ι_L(c) to
the inclusion-point germ and its inverse recovers ι_L(c); C(τ) commutes with each stage
component τ_{Spec L} and with e on every element; and all these germ, naturality, and
stage-map formulas hold for Lc(F), sending up(c) and up(f(c)) at the same finite subfield
stage. -/
def FieldFiniteGaloisStalkLaws : Prop :=
  let C := fieldFiniteGaloisStalkColimit.{u, w} k Ω
  let S := smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)
  let E := fieldFiniteGaloisStalkNatIso.{u, w} k Ω
  let Lc := liftCoefficients.{u, w} (Spec (.of k))
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    E.app Q = fieldFiniteGaloisStalkIso.{u, w} k Ω Q) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    C.map (𝟙 Q) = 𝟙 (C.obj Q)) ∧
  (∀ (Q Q' Q'' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (σ : Q' ⟶ Q''), C.map (τ ≫ σ) = C.map τ ≫ C.map σ) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q).symm
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c) =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (L : FiniteGaloisIntermediateField k Ω),
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L ≫ C.map τ =
      τ.hom.app (op (fieldFiniteGaloisEtale k Ω L)) ≫
        colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q') L) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (c : (colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :
      AddCommGrpCat.{max u w})),
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q' (C.map τ c) =
      S.map τ (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q c)) ∧
  (∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
      (L : FiniteGaloisIntermediateField k Ω)
      (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    E.hom.app (Lc.obj F)
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω (Lc.obj F)) L (ULift.up c)) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))
        (Lc.obj F).obj (ULift.up c)) ∧
  (∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F'),
    C.map (Lc.map f) ≫ E.hom.app (Lc.obj F') =
      E.hom.app (Lc.obj F) ≫ S.map (Lc.map f)) ∧
  ∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F')
      (L : FiniteGaloisIntermediateField k Ω)
      (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    C.map (Lc.map f)
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω (Lc.obj F)) L (ULift.up c)) =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω (Lc.obj F')) L
        (ULift.up (f.hom.app (op (fieldFiniteGaloisEtale k Ω L)) c))

/-- Let k be a field and Ω its prescribed separable closure. The finite Galois neighborhood
functors have the full, faithful, and final properties and the specified point-index lifts;
every section diagram Q(Spec L) has its colimit; and the canonical natural additive comparison
identifies that colimit with the geometric stalk, preserving germs, sheaf maps, and single
coefficient lifts. Both FieldFiniteGaloisColimitLaws and FieldFiniteGaloisStalkLaws hold. -/
theorem original_field_finite_galois_stalk_colimit :
    FieldFiniteGaloisColimitLaws.{u, w} k Ω ∧ FieldFiniteGaloisStalkLaws.{u, w} k Ω := by
  refine ⟨?_, ?_⟩
  · refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, inferInstance,
      ?_, ?_, fieldFiniteGaloisSectionsIndex_original.{u, w} k Ω, ?_, ?_, ?_⟩
    · exact fieldGeometricElementsLiftEquivalence_obj.{u, w} k Ω
    · intro a b f
      exact fieldGeometricElementsLiftEquivalence_map.{u, w} k Ω f
    · exact fieldFiniteGaloisCommonNeighborhoodFunctor_obj.{u, w} k Ω
    · intro L M f
      exact fieldFiniteGaloisCommonNeighborhoodFunctor_map.{u, w} k Ω f
    · intro Q
      infer_instance
    · exact fieldFiniteGaloisSectionDiagram_obj.{u, w} k Ω
    · intro Q L M f
      exact fieldFiniteGaloisSectionDiagram_map.{u, w} k Ω Q f
  · refine ⟨fun _ => rfl,
      (fieldFiniteGaloisStalkColimit.{u, w} k Ω).map_id,
      (fun _ _ _ τ σ => (fieldFiniteGaloisStalkColimit.{u, w} k Ω).map_comp τ σ),
      fieldFiniteGaloisStalkAddEquiv_ι.{u, w} k Ω,
      fieldFiniteGaloisStalkAddEquiv_germ.{u, w} k Ω,
      (fun _ _ τ L => fieldFiniteGaloisStalkColimitMap_ι.{u, w} k Ω τ L),
      (fun _ _ τ c => fieldFiniteGaloisStalkAddEquiv_naturality.{u, w} k Ω τ c),
      fieldFiniteGaloisStalkIso_original_section.{u, w} k Ω,
      (fun _ _ f => fieldFiniteGaloisStalkIso_original_naturality.{u, w} k Ω f),
      (fun _ _ f L c => fieldFiniteGaloisStalkColimitMap_original_ι.{u, w} k Ω f L c)⟩

end AlgebraicGeometry.Scheme.DerivedSections
