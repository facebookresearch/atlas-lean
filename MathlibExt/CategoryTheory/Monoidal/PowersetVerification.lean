/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.MonRelCat
public import MathlibExt.CategoryTheory.Monoidal.SumRelTrace
public import MathlibExt.CategoryTheory.Monoidal.TracedFunctor
public import Mathlib.Order.Hom.Set

/-!
# Powerset verification and invariant feedback

A relation acts on assertions by direct image followed by weakening: an assertion
P relates to Q precisely when every related output of a state in P lies in Q.
This defines a strong symmetric monoidal functor from disjoint-union relations to
preorders and monotone relations. Mathlib's powerset-of-a-sum order isomorphism
provides the tensor comparison.

Finite-path feedback satisfies this partial-correctness condition exactly when
some invariant of the hidden states is preserved by the body. Consequently the
functor preserves the specified symmetric traces, including their comparison
isomorphisms. Divergence alone contributes no output and imposes no termination
obligation. Assertions are arbitrary sets; no assertion syntax is fixed.

This is the full-powerset semantic instance of the verification-functor framework
of Arthan, Martin, Mathiesen and Oliva, A General Framework for Sound and Complete
Floyd-Hoare Logics, Definitions 3.1–3.2 and Section 4.3,
https://arxiv.org/pdf/0807.1016. The invariant argument uses safe hidden states,
with converse soundness by induction on finite executions. It does not assert
syntactic completeness or formalize a program language.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u
namespace CategoryTheory.PowersetVerification
/-- Assertions on a set of states, ordered by inclusion. -/
abbrev assertions (X : SumRelCat.{u}) : MonRelCat.{u} := MonRelCat.of (Set X)
/-- The monotone map of assertions induced by relational direct image. -/
def directImage {X Y : SumRelCat.{u}} (f : X ⟶ Y) : assertions X →o assertions Y :=
  ⟨f.rel.image, SetRel.image_mono⟩
@[simp] theorem directImage_id (X : SumRelCat.{u}) :
    directImage (𝟙 X) = OrderHom.id := by
  ext P x
  simp [directImage]
@[simp] theorem directImage_comp {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    directImage (f ≫ g) = (directImage g).comp (directImage f) := by
  ext P x
  simp only [directImage, SumRelCat.rel_comp, OrderHom.coe_mk, OrderHom.comp_coe,
    Function.comp_apply, SetRel.image_comp]
/-- Send each relation to its partial-correctness relation on full powersets. -/
@[reducible] def verification : SumRelCat.{u} ⥤ MonRelCat.{u} where
  obj := assertions
  map f := MonRelCat.graph (directImage f)
  map_id X := by rw [directImage_id]; rfl
  map_comp f g := by rw [directImage_comp, MonRelCat.graph_comp]
@[simp] theorem map_rel {X Y : SumRelCat.{u}} (f : X ⟶ Y) (P : Set X) (Q : Set Y) :
    (P,Q) ∈ (verification.map f).rel ↔ f.rel.image P ⊆ Q := Iff.rfl

/-- Assemble a pair of assertions into an assertion on the disjoint union. -/
def tensorOrderIso (X Y : SumRelCat.{u}) :
    Set X × Set Y ≃o Set (Sum X Y) := Set.sumEquiv.symm

/-- There is exactly one assertion on the empty state space. -/
def unitOrderIso : MonRelCat.unit.{u} ≃o assertions (𝟙_ SumRelCat.{u}) where
  toFun _ := ∅
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv P := by ext x; exact x.elim
  map_rel_iff' := by intros; simp

/-- The strong tensor comparison in the monotone-relation category. -/
def tensorIso (X Y : SumRelCat.{u}) :
    assertions X ⊗ assertions Y ≅ assertions (X ⊗ Y) := MonRelCat.isoOfOrderIso (tensorOrderIso X Y)
/-- The strong unit comparison. -/
def unitIso : 𝟙_ MonRelCat.{u} ≅ assertions (𝟙_ SumRelCat.{u}) :=
  MonRelCat.isoOfOrderIso unitOrderIso

@[simp] theorem tensorOrderIso_inl (X Y : SumRelCat.{u}) (P : Set X × Set Y) (x : X) :
    Sum.inl x ∈ tensorOrderIso X Y P ↔ x ∈ P.1 := by simp [tensorOrderIso]
@[simp] theorem tensorOrderIso_inr (X Y : SumRelCat.{u}) (P : Set X × Set Y) (y : Y) :
    Sum.inr y ∈ tensorOrderIso X Y P ↔ y ∈ P.2 := by simp [tensorOrderIso]

theorem directImage_tensor {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (P : Set X × Set U) :
    directImage (f ⊗ₘ g) (tensorOrderIso X U P) =
      tensorOrderIso Y V ((directImage f P.1), (directImage g P.2)) := by
  ext z
  cases z <;> simp [directImage, SetRel.mem_image, Sum.exists,
    tensorOrderIso]

private theorem tensor_naturality {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V) :
    (verification.map f ⊗ₘ verification.map g) ≫ (tensorIso Y V).hom =
      (tensorIso X U).hom ≫ verification.map (f ⊗ₘ g) := by
  change MonRelCat.tensor (MonRelCat.graph _) (MonRelCat.graph _) ≫ MonRelCat.graph _ =
    MonRelCat.graph _ ≫ MonRelCat.graph _
  rw [MonRelCat.tensor_graph, MonRelCat.graph_comp, MonRelCat.graph_comp]
  congr 1
  ext P z
  exact (congrArg (fun s => z ∈ s) (directImage_tensor f g P).symm).to_iff

private theorem core_associativity (X Y Z : SumRelCat.{u}) :
    (tensorIso X Y).hom ▷ assertions Z ≫ (tensorIso (X ⊗ Y) Z).hom ≫
        verification.map (α_ X Y Z).hom =
      (α_ (assertions X) (assertions Y) (assertions Z)).hom ≫
        assertions X ◁ (tensorIso Y Z).hom ≫ (tensorIso X (Y ⊗ Z)).hom := by
  change MonRelCat.tensor (MonRelCat.graph _) (𝟙 _) ≫ MonRelCat.graph _ ≫ MonRelCat.graph _ =
    MonRelCat.graph _ ≫ MonRelCat.tensor (𝟙 _) (MonRelCat.graph _) ≫ MonRelCat.graph _
  simp only [MonRelCat.tensor_graph_id, MonRelCat.tensor_id_graph, MonRelCat.graph_comp]
  congr 1
  ext P z
  rcases z with x | y | z <;>
    simp [directImage, SetRel.mem_image, Sum.exists, OrderIso.prodAssoc,
      tensorOrderIso, Set.sumEquiv, OrderHom.comp, OrderHom.prodMap] <;> rfl

private theorem core_left_unit (X : SumRelCat.{u}) :
    (λ_ (assertions X)).hom = unitIso.hom ▷ assertions X ≫
      (tensorIso (𝟙_ SumRelCat) X).hom ≫ verification.map (λ_ X).hom := by
  change MonRelCat.graph _ = MonRelCat.tensor (MonRelCat.graph _) (𝟙 _) ≫
    MonRelCat.graph _ ≫ MonRelCat.graph _
  simp only [MonRelCat.tensor_graph_id, MonRelCat.graph_comp]
  congr 1
  ext P x
  simp [directImage, SetRel.mem_image,
    tensorOrderIso, Set.sumEquiv, unitOrderIso, OrderHom.comp, OrderHom.prodMap,
    MonRelCat.leftUnitOrderIso]

private theorem core_right_unit (X : SumRelCat.{u}) :
    (ρ_ (assertions X)).hom = assertions X ◁ unitIso.hom ≫
      (tensorIso X (𝟙_ SumRelCat)).hom ≫ verification.map (ρ_ X).hom := by
  change MonRelCat.graph _ = MonRelCat.tensor (𝟙 _) (MonRelCat.graph _) ≫
    MonRelCat.graph _ ≫ MonRelCat.graph _
  simp only [MonRelCat.tensor_id_graph, MonRelCat.graph_comp]
  congr 1
  ext P x
  simp [directImage, SetRel.mem_image,
    tensorOrderIso, Set.sumEquiv, unitOrderIso, OrderHom.comp, OrderHom.prodMap,
    MonRelCat.rightUnitOrderIso]

/-- Coherence of the powerset tensor and unit comparisons. -/
def coreMonoidal : verification.{u}.CoreMonoidal where
  εIso := unitIso
  μIso := tensorIso
  μIso_hom_natural_left f U := by
    have h := tensor_naturality f (𝟙 U)
    erw [verification.map_id, tensorHom_id, tensorHom_id] at h
    exact h
  μIso_hom_natural_right U f := by
    have h := tensor_naturality (𝟙 U) f
    erw [verification.map_id, id_tensorHom, id_tensorHom] at h
    exact h
  associativity := by exact core_associativity
  left_unitality := by exact core_left_unit
  right_unitality := by exact core_right_unit
/-- Powerset verification is strong monoidal. -/
instance : verification.{u}.Monoidal := coreMonoidal.toMonoidal
/-- Powerset verification preserves the symmetry. -/
instance : verification.{u}.Braided where
  braided X Y := by
    change MonRelCat.graph _ ≫ MonRelCat.graph _ = MonRelCat.graph _ ≫ MonRelCat.graph _
    simp only [MonRelCat.graph_comp]
    congr 1
    ext P z
    cases z <;> simp [directImage, SetRel.mem_image, Sum.exists,
      OrderIso.prodComm, tensorOrderIso, Set.sumEquiv, OrderHom.comp] <;> rfl

/-- The hidden states from which every terminating execution satisfies the postcondition. -/
def safeInvariant {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (R : Set Y) : Set U :=
  {u | ∀ y, SumRelCat.FeedbackPath f (Sum.inr u) y → y ∈ R}

/-- Partial correctness of feedback is equivalent to preservation of a hidden invariant. -/
theorem feedback_image_subset_iff {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U)
    (P : Set X) (R : Set Y) :
    (SumRelCat.feedback f).rel.image P ⊆ R ↔
      ∃ Q : Set U, f.rel.image (tensorOrderIso X U (P,Q)) ⊆ tensorOrderIso Y U (R,Q) := by
  constructor
  · intro h
    refine ⟨safeInvariant f R, ?_⟩
    rintro t ⟨s, hs, hf⟩
    cases s with
    | inl x =>
      have hx : x ∈ P := (tensorOrderIso_inl X U _ x).mp hs
      cases t with
      | inl y => exact (tensorOrderIso_inl Y U _ y).mpr (h ⟨x, hx, .output hf⟩)
      | inr v =>
        apply (tensorOrderIso_inr Y U _ v).mpr
        intro y hp
        exact h ⟨x, hx, SumRelCat.FeedbackPath.step hf hp⟩
    | inr u =>
      have hu : u ∈ safeInvariant f R := (tensorOrderIso_inr X U _ u).mp hs
      cases t with
      | inl y => exact (tensorOrderIso_inl Y U _ y).mpr (hu y (.output hf))
      | inr v => exact (tensorOrderIso_inr Y U _ v).mpr (fun y hp => hu y (.step hf hp))
  · rintro ⟨Q, hQ⟩ y ⟨x, hx, hp⟩
    have sound : ∀ {s : Sum X U} {y : Y}, SumRelCat.FeedbackPath f s y →
        s ∈ tensorOrderIso X U (P,Q) → y ∈ R := by
      intro s y hp
      induction hp with
      | output hf =>
        intro hs
        exact (tensorOrderIso_inl Y U _ _).mp (hQ ⟨_, hs, hf⟩)
      | step hf _ ih =>
        intro hs
        exact ih ((tensorOrderIso_inr X U _ _).mpr
          ((tensorOrderIso_inr Y U _ _).mp (hQ ⟨_, hs, hf⟩)))
    exact sound hp ((tensorOrderIso_inl X U _ x).mpr hx)

/-- The comparison-conjugated image relation acts on pairs of assertions. -/
theorem comparison_rel {X Y U V : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ V)
    (P : Set X × Set U) (R : Set Y × Set V) :
    (P,R) ∈ (Functor.LaxMonoidal.μ verification X U ≫ verification.map f ≫
      Functor.OplaxMonoidal.δ verification Y V).rel ↔
      f.rel.image (tensorOrderIso X U P) ⊆ tensorOrderIso Y V R := by
  change (P,R) ∈ ((MonRelCat.isoOfOrderIso (X := MonRelCat.prod (assertions X) (assertions U))
      (Y := assertions (X ⊗ U)) (tensorOrderIso X U)).hom ≫ verification.map f ≫
      (MonRelCat.isoOfOrderIso (X := assertions (Y ⊗ V))
        (Y := MonRelCat.prod (assertions Y) (assertions V)) (tensorOrderIso Y V).symm).hom).rel ↔ _
  erw [MonRelCat.isoOfOrderIso_hom_comp_rel, MonRelCat.comp_isoOfOrderIso_hom_rel]
  rfl

/-- Finite-path feedback becomes existential invariant feedback on assertions. -/
theorem preserves_trace :
    SumRelCat.symmetricTrace.{u}.Preserves MonRelCat.symmetricTrace verification := by
  intro X Y U f
  apply MonRelCat.Hom.ext
  ext ⟨P,R⟩
  change (SumRelCat.feedback f).rel.image P ⊆ R ↔
    ∃ Q : Set U, ((P,Q),(R,Q)) ∈ (Functor.LaxMonoidal.μ verification X U ≫ verification.map f ≫
      Functor.OplaxMonoidal.δ verification Y U).rel
  exact (feedback_image_subset_iff f P R).trans
    (exists_congr fun Q => (comparison_rel f (P,Q) (R,Q)).symm)
end CategoryTheory.PowersetVerification
