/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels

/-!
# Actual analytic-adic diamondification maps

The input analytic spaces have actual all-rank valued affinoid models.
The raw diamond functor is the native left Kan extension of the actual
untilt-to-analytic mapping presheaf along the fixed local tilt functor.
Its elements are assembled from actual untilt maps by the Kan unit.
Sheafification then gives its fixed v-sheaf, functorially in the analytic
space. The comparison with marked untilt isomorphism classes is stated
on this actual prescribed map, rather than an arbitrary equivalence.

Source: Scholze, arXiv:1709.07343v4, Definition 15.5 and Lemma 15.6.
The marked untilt formula, diamond presentation and etale-site
equivalence remain separate direct construction/proof requests.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open AffinePerfectoidVSite AffineUntiltingGeometry AnalyticTateAdicModels

variable (p : ℕ) [Fact p.Prime]

/-- An actual affinoid model is analytic, by its single identity chart. -/
def affineObject {P : TatePair p} (M : AffinoidModel p P) : AnalyticAdicSpace p :=
  ⟨M.valued, by
    refine ⟨PUnit.{2}, fun _ ↦ P, fun _ ↦ M, fun _ ↦ 𝟙 M.valued, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact IsOpenEmbedding.id
    · intro i x
      change IsIso ((𝟙 M.valued.space : M.valued.space ⟶ M.valued.space).stalkMap x)
      rw [LocallyRingedSpace.stalkMap_id]
      exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
    · intro i U _
      change @IsHomeomorph _ _ (M.valued.sectionTopology U) (M.valued.sectionTopology U) id
      exact @IsHomeomorph.id _ (M.valued.sectionTopology U)
    · intro U
      apply le_antisymm
      · exact le_iInf fun V ↦ le_iInf fun h ↦ le_iInf fun _ ↦
          continuous_iff_le_induced.mp (M.continuous_restrict p h)
      · refine iInf_le_of_le U (iInf_le_of_le le_rfl (iInf_le_of_le ⟨PUnit.unit, ?_⟩ ?_))
        · intro x _
          exact ⟨x, rfl⟩
        · have hid : ⇑(M.valued.space.presheaf.map (homOfLE (le_refl U)).op).hom = id := by
            have : (homOfLE (le_refl U)).op = 𝟙 (op U) := Subsingleton.elim _ _
            rw [this, CategoryTheory.Functor.map_id]
            rfl
          rw [hid, @induced_id _ (M.valued.sectionTopology U)]
    · intro x
      exact ⟨PUnit.unit, x, rfl⟩⟩

/-- The local actual realization functor, with the declared point/coordinate normalization. -/
def realizationFunctor (R : AffineRealization p) :
    AffineUntilting p ⥤ AnalyticAdicSpace p where
  obj P := affineObject p (R.model P)
  map f := ObjectProperty.homMk (R.map f)
  map_id P := by
    apply ObjectProperty.hom_ext
    exact R.identity P
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact R.composition f g

/-- Actual analytic maps from every untilt, retaining every target map. -/
def analyticMapsFunctor (R : AffineRealization p) :
    AnalyticAdicSpace p ⥤ ((AffineUntilting p)ᵒᵖ ⥤ Type 1) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (realizationFunctor p R).op ⋙
    (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{1, 0})

/-- The raw diamond functor is the actual Kan extension of the untilt mapping functor. -/
def rawDiamondFunctor (R : AffineRealization p) :
    AnalyticAdicSpace p ⥤ ((Affine p)ᵒᵖ ⥤ Type 1) :=
  analyticMapsFunctor p R ⋙ (tiltFunctor p).op.lan

/-- Its fixed functorial v-sheafification. -/
def diamondFunctor (R : AffineRealization p) : AnalyticAdicSpace p ⥤ VSheaf p :=
  rawDiamondFunctor p R ⋙ presheafToSheaf (topology p) (Type 1)

/-- A marked actual affine untilt and its actual analytic map. -/
structure UntiltingWitness (R : AffineRealization p) (Y : AnalyticAdicSpace p)
    (P : Affine p) where
  affine : AffineUntilting p
  tiltIso : affine.tilt.pair ≅ P
  map : (realizationFunctor p R).obj affine ⟶ Y

variable {p}

/-- Isomorphism of marked untilts, preserving the actual analytic map. -/
def IsomorphicWitness {R : AffineRealization p} {Y : AnalyticAdicSpace p}
    {P : Affine p} (a b : UntiltingWitness p R Y P) : Prop :=
  ∃ e : a.affine ≅ b.affine,
    (tiltFunctor p).mapIso e ≪≫ b.tiltIso = a.tiltIso ∧
      (realizationFunctor p R).map e.hom ≫ b.map = a.map

/-- The actual marked-untilt isomorphism relation. -/
def witnessSetoid {R : AffineRealization p} {Y : AnalyticAdicSpace p}
    (P : Affine p) : Setoid (UntiltingWitness p R Y P) where
  r := IsomorphicWitness
  iseqv :=
    ⟨fun a ↦ ⟨Iso.refl _, by simp, by simp⟩,
      fun {a b} ⟨e, h, h'⟩ ↦ ⟨e.symm, by rw [← h]; simp,
        by rw [← h']; simp⟩,
      fun {a b c} ⟨e, h, h'⟩ ⟨f, k, k'⟩ ↦ ⟨e ≪≫ f,
        by simp only [Functor.mapIso_trans, Iso.trans_assoc, k, h],
        by simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, k', h']⟩⟩

/-- The source's actual isomorphism classes of marked untilts. -/
abbrev UntiltingClasses {R : AffineRealization p} {Y : AnalyticAdicSpace p}
    (P : Affine p) := Quotient (witnessSetoid (R := R) (Y := Y) P)

/-- The prescribed Kan-unit map from each marked actual untilt. -/
def witnessMap {R : AffineRealization p} {Y : AnalyticAdicSpace p}
    {P : Affine p} (a : UntiltingWitness p R Y P) :
    ((rawDiamondFunctor p R).obj Y).obj (op P) :=
  ((rawDiamondFunctor p R).obj Y).map a.tiltIso.inv.op
    (((tiltFunctor p).op.lanUnit.app ((analyticMapsFunctor p R).obj Y)).app
      (op a.affine) (ULift.up a.map))

/-- The Kan-unit map identifies isomorphic marked untilts. -/
theorem witnessMap_isomorphic {R : AffineRealization p} {Y : AnalyticAdicSpace p}
    {P : Affine p} {a b : UntiltingWitness p R Y P} (h : IsomorphicWitness a b) :
    witnessMap a = witnessMap b := by
  obtain ⟨e, he, hm⟩ := h
  let M := (analyticMapsFunctor p R).obj Y
  let N := (rawDiamondFunctor p R).obj Y
  let η := (tiltFunctor p).op.lanUnit.app M
  have hη := congrArg (fun q ↦ q (ULift.up b.map)) (η.naturality e.hom.op)
  have hM : M.map e.hom.op (ULift.up b.map) = ULift.up a.map := by
    apply ULift.ext
    exact hm
  change η.app (op a.affine) (M.map e.hom.op (ULift.up b.map)) =
    N.map e.hom.tilted.op (η.app (op b.affine) (ULift.up b.map)) at hη
  rw [hM] at hη
  have ht : a.tiltIso.inv ≫ e.hom.tilted = b.tiltIso.inv := by
    rw [← he]
    change b.tiltIso.inv ≫ (tiltFunctor p).map e.inv ≫
      (tiltFunctor p).map e.hom = b.tiltIso.inv
    rw [← Functor.map_comp, e.inv_hom_id]
    change b.tiltIso.inv ≫ 𝟙 _ = b.tiltIso.inv
    exact Category.comp_id _
  change N.map a.tiltIso.inv.op (η.app (op a.affine) (ULift.up a.map)) =
    N.map b.tiltIso.inv.op (η.app (op b.affine) (ULift.up b.map))
  rw [hη]
  rw [← types_comp_apply, ← N.map_comp]
  rw [← op_comp, ht]

/-- The fixed comparison from source marked-untilt classes to the native raw diamond. -/
def classComparison {R : AffineRealization p} {Y : AnalyticAdicSpace p}
    (P : Affine p) : UntiltingClasses (R := R) (Y := Y) P →
    ((rawDiamondFunctor p R).obj Y).obj (op P) :=
  Quotient.lift witnessMap (fun _ _ h ↦ witnessMap_isomorphic h)

end MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
