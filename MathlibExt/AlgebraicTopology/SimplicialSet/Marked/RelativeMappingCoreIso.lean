/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMappingCore
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPrismCriterion

/-!
# The actual maximal fixed-base mapping complexes are native cores

For the intrinsic Cartesian or cocartesian marking of an inner fibration
over a quasicategory, the maximally parameter-marked fixed-base mapping
complex is isomorphic to the full native function core on marked-map
vertices. Both directions retain the entire original prism and the original
base-point coordinate. The native core comparison proves Kan fibrancy;
neither a Kan base nor a marked model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

private inductive Orientation
  | cartesian
  | cocartesian

private def total (o : Orientation) {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] : Marked.{u} where
  toSSet := E
  marking := match o with
    | .cartesian => (cartesian p).marking
    | .cocartesian => (cocartesian p).marking
  degenerate_mem x := by
    cases o
    · exact (cartesian p).degenerate_mem x
    · exact (cocartesian p).degenerate_mem x

private def projection (o : Orientation) {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] : total o p ⟶ max B := toMax p

private theorem projection_inner (o : Orientation) {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] : InnerFibration (projection o p).hom := by
  exact inferInstanceAs (InnerFibration p)

private theorem total_quasicategory (o : Orientation) {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] : Quasicategory (total o p).toSSet := by
  exact @quasicategory_of_innerFibration E B p (inferInstanceAs (InnerFibration p))
    (inferInstanceAs (Quasicategory B))

private theorem maxPrism_mem_core (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (n : SimplexCategoryᵒᵖ) (f : (mappingComplex .maximal X (total o p)).obj n)
    (hf : f.hom ≫ p = CartesianMonoidalCategory.snd (SSet.stdSimplex.obj n.unop) X.toSSet ≫ r.hom) :
    f.hom ∈ (core (parameterMapping X.toSSet (total o p).toSSet)).obj n := by
  let _ : Quasicategory E := quasicategory_of_innerFibration p
  cases o
  · let F : SSet.stdSimplex.obj n.unop ⊗ X.toSSet ⟶ E := f.hom
    let f' : prod (min (SSet.stdSimplex.obj n.unop)) X ⟶ cartesian p :=
      ⟨F, fun he => @f.preserve _ ⟨Set.mem_univ _, he.2⟩⟩
    apply (mem_core_parameterMapping_iff F).mpr
    exact (preserves_maxParameter_cartesian_iff p r.hom f' hf).mp (fun e he => @f.preserve e he)
  · let F : SSet.stdSimplex.obj n.unop ⊗ X.toSSet ⟶ E := f.hom
    let f' : prod (min (SSet.stdSimplex.obj n.unop)) X ⟶ cocartesian p :=
      ⟨F, fun he => @f.preserve _ ⟨Set.mem_univ _, he.2⟩⟩
    apply (mem_core_parameterMapping_iff F).mpr
    exact (preserves_maxParameter_cocartesian_iff p r.hom f' hf).mp (fun e he => @f.preserve e he)

private theorem corePrism_preserves (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (n : SimplexCategoryᵒᵖ) (f : (mappingComplex .minimal X (total o p)).obj n)
    (hf : f.hom ≫ p = CartesianMonoidalCategory.snd (SSet.stdSimplex.obj n.unop) X.toSSet ≫ r.hom)
    (hc : f.hom ∈ (core (parameterMapping X.toSSet (total o p).toSSet)).obj n) :
    ∀ e : (prod (max (SSet.stdSimplex.obj n.unop)) X).toSSet _⦋1⦌,
      e ∈ (prod (max (SSet.stdSimplex.obj n.unop)) X).marking →
        f.hom.app (op ⦋1⦌) e ∈ (total o p).marking := by
  let _ : Quasicategory (total o p).toSSet := total_quasicategory o p
  cases o
  · exact (preserves_maxParameter_cartesian_iff p r.hom f hf).mpr
      ((mem_core_parameterMapping_iff f.hom).mp hc)
  · exact (preserves_maxParameter_cocartesian_iff p r.hom f hf).mpr
      ((mem_core_parameterMapping_iff f.hom).mp hc)

private def promoteCore (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingCore r (projection o p) ⟶ mappingComplex .maximal X (total o p) where
  app n := ↾fun t =>
    { hom := ((relativeMappingCoreToMin r (projection o p)).app n t).hom
      preserve := fun he => corePrism_preserves o r p n
        ((relativeMappingCoreToMin r (projection o p)).app n t)
        (relativeMappingCoreToMin_prism_over r (projection o p) n t)
        (relativeMappingCoreToMin_mem_core r (projection o p) n t) _ he }
  naturality n m a := by
    ext t
    apply Hom.ext
    have h := NatTrans.naturality_apply (relativeMappingCoreToMin r (projection o p)) a t
    have h' := congrArg Hom.hom h
    exact h'

private theorem promoteCore_to_min (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    promoteCore o r p ≫ mappingComplexMaxToMin X (total o p) =
      relativeMappingCoreToMin r (projection o p) := by
  ext n t
  apply Hom.ext
  ext m e
  rfl

private theorem maxToMin_mono (X Y : Marked.{u}) : Mono (mappingComplexMaxToMin X Y) := by
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono ((mappingComplexMaxToMin X Y).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (mappingComplexMaxToMin_app_injective X Y n)
  exact NatTrans.mono_of_mono_app _

private theorem maxToMin_point {X Z : Marked.{u}} (r : X ⟶ Z) :
    mappingBasePoint .maximal r ≫ mappingComplexMaxToMin X Z = mappingBasePoint .minimal r := by
  apply SSet.yonedaEquiv.injective
  dsimp only [mappingBasePoint]
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Hom.ext
  rw [mappingComplexMaxToMin_app_hom]
  rfl

private theorem promoteCore_over (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    promoteCore o r p ≫ mappingComplexPost .maximal X (projection o p) =
      relativeMappingCoreToUnderlying r (projection o p) ≫
        pullback.snd (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r) ≫
          mappingBasePoint .maximal r := by
  let _ : Mono (mappingComplexMaxToMin X (max B)) := maxToMin_mono X (max B)
  apply (cancel_mono (mappingComplexMaxToMin X (max B))).mp
  rw [Category.assoc, ← mappingComplexMaxToMin_post, ← Category.assoc,
    promoteCore_to_min, relativeMappingCoreToMin_post]
  let a : parameterRelative r (projection o p) ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r)
  let j : relativeMappingCore r (projection o p) ⟶ parameterRelative r (projection o p) :=
    relativeMappingCoreToUnderlying r (projection o p)
  change j ≫ a ≫ mappingBasePoint .minimal r =
    (j ≫ a ≫ mappingBasePoint .maximal r) ≫ mappingComplexMaxToMin X (max B)
  simp only [Category.assoc, maxToMin_point]

private def back (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingCore r (projection o p) ⟶ relativeMappingComplex .maximal r (projection o p) :=
  pullback.lift (promoteCore o r p)
    (relativeMappingCoreToUnderlying r (projection o p) ≫
      pullback.snd (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r))
        (promoteCore_over o r p)

private theorem maxToMin_underlying (X Y : Marked.{u}) :
    mappingComplexMaxToMin X Y ≫ mappingComplexUnderlying .minimal X Y =
      mappingComplexUnderlying .maximal X Y := by
  ext n f
  exact mappingComplexMaxToMin_app_hom X Y n f

private theorem back_forget (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    back o r p ≫ relativeMappingForget .maximal r (projection o p) =
      relativeMappingCoreToUnderlying r (projection o p) := by
  let a : parameterRelative r (projection o p) ⟶ parameterMapping X.toSSet (total o p).toSSet :=
    pullback.fst (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r)
  let b : parameterRelative r (projection o p) ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r)
  let q := relativeMappingForget .maximal r (projection o p)
  let f := back o r p
  let j := relativeMappingCoreToUnderlying r (projection o p)
  let c : relativeMappingComplex .maximal r (projection o p) ⟶ mappingComplex .maximal X (total o p) :=
    pullback.fst (mappingComplexPost .maximal X (projection o p)) (mappingBasePoint .maximal r)
  let d : relativeMappingComplex .maximal r (projection o p) ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost .maximal X (projection o p)) (mappingBasePoint .maximal r)
  have hqa : q ≫ a = c ≫ mappingComplexUnderlying .maximal X (total o p) :=
    relativeMappingForget_fst .maximal r (projection o p)
  have hqb : q ≫ b = d := relativeMappingForget_snd .maximal r (projection o p)
  have hfa : f ≫ c = promoteCore o r p := pullback.lift_fst _ _ _
  have hfb : f ≫ d = j ≫ b := pullback.lift_snd _ _ _
  have hp : promoteCore o r p ≫ mappingComplexUnderlying .maximal X (total o p) = j ≫ a := by
    rw [← maxToMin_underlying, ← Category.assoc, promoteCore_to_min]
    exact relativeMappingCoreToMin_forget r (projection o p)
  apply pullback.hom_ext
  · change (f ≫ q) ≫ a = j ≫ a
    rw [Category.assoc, hqa, ← Category.assoc, hfa, hp]
  · change (f ≫ q) ≫ b = j ≫ b
    rw [Category.assoc, hqb, hfb]

private theorem range_forget_le_core (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Subcomplex.range (relativeMappingForget .maximal r (projection o p)) ≤
      core (parameterRelative r (projection o p)) := by
  let _ : InnerFibration (projection o p).hom := projection_inner o p
  let _ : Quasicategory (max B).toSSet := inferInstanceAs (Quasicategory B)
  apply (le_core_iff _).mpr
  intro e he
  obtain ⟨t, rfl⟩ := he
  have ht : (relativeMappingForget .maximal r (projection o p)).app (op ⦋1⦌) t ∈
      (core (parameterRelative r (projection o p))).obj (op ⦋1⦌) := by
    apply (mem_core_parameterRelative_iff r (projection o p) (op ⦋1⦌) _).mpr
    let f := (pullback.fst (mappingComplexPost .maximal X (projection o p))
      (mappingBasePoint .maximal r)).app (op ⦋1⦌) t
    have hp := ConcreteCategory.congr_hom
      (congr_app (relativeMappingForget_fst .maximal r (projection o p)) (op ⦋1⦌)) t
    change (pullback.fst (parameterMappingPost X.toSSet (projection o p).hom)
      (parameterBasePoint r)).app (op ⦋1⦌)
        ((relativeMappingForget .maximal r (projection o p)).app (op ⦋1⦌) t) = f.hom at hp
    exact hp.symm ▸ maxPrism_mem_core o r p (op ⦋1⦌) f
      (relativeMapping_prism_over .maximal r (projection o p) (op ⦋1⦌) t)
  exact mem_core_obj_one_iff.mp ht

private def coreFactor (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (projection o p) ⟶
      (core (parameterRelative r (projection o p)) : SSet.{u}) :=
  Subcomplex.lift (relativeMappingForget .maximal r (projection o p)) (range_forget_le_core o r p)

private theorem range_coreFactor_le_full (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Subcomplex.range (coreFactor o r p) ≤ Subcomplex.full (relativeMappingCoreVertices r (projection o p)) := by
  apply (Subcomplex.le_full_iff (Subcomplex.range (coreFactor o r p))).mpr
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  let f := (pullback.fst (mappingComplexPost .maximal X (projection o p))
    (mappingBasePoint .maximal r)).app (op ⦋0⦌) t
  let f' := (mappingComplexMaxToMin X (total o p)).app (op ⦋0⦌) f
  have hf : f'.hom ∈ markedMappingVertices X (total o p) :=
    Subcomplex.mem_full_obj_zero_iff.mp ((mappingComplexMinFullIso X (total o p)).hom.app (op ⦋0⦌) f').property
  have hp := ConcreteCategory.congr_hom
    (congr_app (relativeMappingForget_fst .maximal r (projection o p)) (op ⦋0⦌)) t
  have h' : ((core (parameterRelative r (projection o p))).ι ≫
      pullback.fst (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r)).app (op ⦋0⦌)
        ((coreFactor o r p).app (op ⦋0⦌) t) = f'.hom :=
    hp.trans (mappingComplexMaxToMin_app_hom X (total o p) (op ⦋0⦌) f).symm
  change ((core (parameterRelative r (projection o p))).ι ≫
      pullback.fst (parameterMappingPost X.toSSet (projection o p).hom) (parameterBasePoint r)).app (op ⦋0⦌)
        ((coreFactor o r p).app (op ⦋0⦌) t) ∈ markedMappingVertices X (total o p)
  exact h'.symm ▸ hf

private def front (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (projection o p) ⟶ relativeMappingCore r (projection o p) :=
  Subcomplex.lift (coreFactor o r p) (range_coreFactor_le_full o r p)

private theorem front_forget (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    front o r p ≫ relativeMappingCoreToUnderlying r (projection o p) =
      relativeMappingForget .maximal r (projection o p) := by
  ext n t
  rfl

private def comparisonIso (o : Orientation) {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (projection o p) ≅ relativeMappingCore r (projection o p) where
  hom := front o r p
  inv := back o r p
  hom_inv_id := by
    let _ : Mono (relativeMappingForget .maximal r (projection o p)) :=
      relativeMappingForget_mono .maximal r (projection o p)
    apply (cancel_mono (relativeMappingForget .maximal r (projection o p))).mp
    rw [Category.assoc, back_forget, front_forget, Category.id_comp]
  inv_hom_id := by
    let _ : Mono (relativeMappingCoreToUnderlying r (projection o p)) :=
      relativeMappingCoreToUnderlying_mono r (projection o p)
    apply (cancel_mono (relativeMappingCoreToUnderlying r (projection o p))).mp
    rw [Category.assoc, front_forget, back_forget, Category.id_comp]

/-- The actual maximally parameter-marked Cartesian fixed-base complex is the native core on marked-map vertices. -/
def cartesianMappingCoreIso {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (cartesianProjection p) ≅
      relativeMappingCore r (cartesianProjection p) := comparisonIso .cartesian r p

/-- The actual cocartesian fixed-base complex has the same native full-core description. -/
def cocartesianMappingCoreIso {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (cocartesianProjection p) ≅
      relativeMappingCore r (cocartesianProjection p) := comparisonIso .cocartesian r p

/-- The Cartesian comparison retains every original complete prism and fixed-base point. -/
theorem cartesianMappingCoreIso_hom_forget {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    (cartesianMappingCoreIso r p).hom ≫ relativeMappingCoreToUnderlying r (cartesianProjection p) =
      relativeMappingForget .maximal r (cartesianProjection p) := front_forget .cartesian r p

/-- The cocartesian comparison retains those same original coordinates. -/
theorem cocartesianMappingCoreIso_hom_forget {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    (cocartesianMappingCoreIso r p).hom ≫ relativeMappingCoreToUnderlying r (cocartesianProjection p) =
      relativeMappingForget .maximal r (cocartesianProjection p) := front_forget .cocartesian r p

/-- Original intrinsic Cartesian fixed-base mapping complexes are Kan over any quasicategory base. -/
theorem cartesian_relativeMapping_kanComplex {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    KanComplex (relativeMappingComplex .maximal r (cartesianProjection p)) := by
  let _ : InnerFibration (cartesianProjection p).hom := inferInstanceAs (InnerFibration p)
  let _ : KanComplex (relativeMappingCore r (cartesianProjection p)) :=
    relativeMappingCore_kanComplex r (cartesianProjection p)
  let _ : Fibration (cartesianMappingCoreIso r p).hom := inferInstance
  exact isFibrant_of_fibration (cartesianMappingCoreIso r p).hom

/-- The native cocartesian fixed-base mapping complex is Kan under the same genuine hypotheses. -/
theorem cocartesian_relativeMapping_kanComplex {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    KanComplex (relativeMappingComplex .maximal r (cocartesianProjection p)) := by
  let _ : InnerFibration (cocartesianProjection p).hom := inferInstanceAs (InnerFibration p)
  let _ : KanComplex (relativeMappingCore r (cocartesianProjection p)) :=
    relativeMappingCore_kanComplex r (cocartesianProjection p)
  let _ : Fibration (cocartesianMappingCoreIso r p).hom := inferInstance
  exact isFibrant_of_fibration (cocartesianMappingCoreIso r p).hom

end SSet.Marked
