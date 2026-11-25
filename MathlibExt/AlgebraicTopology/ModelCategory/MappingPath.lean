/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Mapping paths retaining both original endpoints

A good path object of the original target gives a mapping-path object of
an arbitrary arrow. At a fibrant original target, its source projection is
a trivial fibration. When the original source is fibrant, its target
projection is a fibration; a weak original arrow between fibrant objects
makes that target projection trivial as well. No right
properness or Cartesian model assumption is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.MappingPath

variable {C : Type u} [Category.{v} C]

section Categorical

variable [HasPullbacks C]
  {X Y : C} (f : X ⟶ Y) (P : PrepathObject Y)

/-- The original source and the first endpoint determine the path pullback. -/
abbrev Object : C := pullback f P.p₀

/-- The original source projection. -/
abbrev source : Object f P ⟶ X := pullback.fst f P.p₀

/-- The complete path in the original target's given path object. -/
abbrev path : Object f P ⟶ P.P := pullback.snd f P.p₀

/-- The far endpoint of that same path. -/
def target : Object f P ⟶ Y := path f P ≫ P.p₁

/-- The original arrow embeds by its original constant path. -/
def sectionMap : X ⟶ Object f P :=
  pullback.lift (𝟙 X) (f ≫ P.ι) (by simp)

@[reassoc (attr := simp)]
theorem sectionMap_source : sectionMap f P ≫ source f P = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sectionMap_path : sectionMap f P ≫ path f P = f ≫ P.ι :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem sectionMap_target : sectionMap f P ≫ target f P = f := by
  dsimp only [target]
  rw [← Category.assoc, sectionMap_path, Category.assoc, P.ι_p₁, Category.comp_id]

/-- The path's starting endpoint is exactly the image of the original source. -/
@[reassoc]
theorem path_start : path f P ≫ P.p₀ = source f P ≫ f :=
  (pullback.condition (f := f) (g := P.p₀)).symm

variable [HasBinaryProducts C]

/-- The original source and far endpoint form a single endpoint pair. -/
def endpointPair : Object f P ⟶ X ⨯ Y := prod.lift (source f P) (target f P)

@[reassoc (attr := simp)]
theorem endpointPair_fst : endpointPair f P ≫ prod.fst = source f P :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem endpointPair_snd : endpointPair f P ≫ prod.snd = target f P :=
  prod.lift_snd _ _

/-- The endpoint-pair map is the literal base change of the path object's endpoint map. -/
theorem endpointPair_isPullback :
    IsPullback (endpointPair f P) (path f P) (prod.map f (𝟙 Y)) P.p := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply prod.hom_ext
    · simpa only [Category.assoc, prod.map_fst, Category.comp_id,
        endpointPair_fst_assoc, PrepathObject.p_fst] using (path_start f P).symm
    · simp [Category.assoc, target]
  · intro T a b h₀ h₁
    apply pullback.hom_ext
    · simpa only [Category.assoc, endpointPair_fst] using
        congrArg (fun k => k ≫ prod.fst) h₀
    · exact h₁
  · intro T a b h
    have h₀ : (a ≫ prod.fst) ≫ f = b ≫ P.p₀ := by
      simpa only [Category.assoc, prod.map_fst, Category.comp_id,
        PrepathObject.p_fst] using congrArg (fun k => k ≫ prod.fst) h
    let l : T ⟶ Object f P := pullback.lift (a ≫ prod.fst) b h₀
    refine ⟨l, ?_, ?_⟩
    · apply prod.hom_ext
      · simp [l, Category.assoc]
      · have h₁ : b ≫ P.p₁ = a ≫ prod.snd := by
          simpa only [Category.assoc, prod.map_snd, Category.comp_id,
            PrepathObject.p_snd] using
            (congrArg (fun k => k ≫ prod.snd) h).symm
        rw [Category.assoc, endpointPair_snd]
        dsimp only [target]
        rw [← Category.assoc]
        change (pullback.lift (a ≫ prod.fst) b h₀ ≫ pullback.snd f P.p₀) ≫ P.p₁ = _
        rw [pullback.lift_snd]
        exact h₁
    · simp [l]

variable {X' Y' : C}

/-- A map of original arrows and their path objects acts on the same path pullback. -/
def map (f' : X' ⟶ Y') (P' : PrepathObject Y')
    (g : X ⟶ X') (k : Y ⟶ Y') (l : P.P ⟶ P'.P)
    (h : g ≫ f' = f ≫ k) (h₀ : l ≫ P'.p₀ = P.p₀ ≫ k) :
    Object f P ⟶ Object f' P' :=
  pullback.lift (source f P ≫ g) (path f P ≫ l) (by
    rw [Category.assoc, h, ← Category.assoc, ← path_start, Category.assoc, ← h₀,
      ← Category.assoc])

omit [HasBinaryProducts C] in
@[reassoc (attr := simp)]
theorem map_source (f' : X' ⟶ Y') (P' : PrepathObject Y')
    (g : X ⟶ X') (k : Y ⟶ Y') (l : P.P ⟶ P'.P) (h) (h₀) :
    map f P f' P' g k l h h₀ ≫ source f' P' = source f P ≫ g :=
  pullback.lift_fst _ _ _

omit [HasBinaryProducts C] in
@[reassoc (attr := simp)]
theorem map_path (f' : X' ⟶ Y') (P' : PrepathObject Y')
    (g : X ⟶ X') (k : Y ⟶ Y') (l : P.P ⟶ P'.P) (h) (h₀) :
    map f P f' P' g k l h h₀ ≫ path f' P' = path f P ≫ l :=
  pullback.lift_snd _ _ _

omit [HasBinaryProducts C] in
/-- The far-endpoint square is derived from the same original path map. -/
@[reassoc]
theorem map_target (f' : X' ⟶ Y') (P' : PrepathObject Y')
    (g : X ⟶ X') (k : Y ⟶ Y') (l : P.P ⟶ P'.P) (h) (h₀)
    (h₁ : l ≫ P'.p₁ = P.p₁ ≫ k) :
    map f P f' P' g k l h h₀ ≫ target f' P' = target f P ≫ k := by
  dsimp only [target]
  rw [← Category.assoc, map_path, Category.assoc, h₁, ← Category.assoc]

omit [HasBinaryProducts C] in
/-- Compatibility of the supplied path units preserves the exact original source section. -/
theorem sectionMap_map (f' : X' ⟶ Y') (P' : PrepathObject Y')
    (g : X ⟶ X') (k : Y ⟶ Y') (l : P.P ⟶ P'.P) (h) (h₀)
    (hι : P.ι ≫ l = k ≫ P'.ι) :
    sectionMap f P ≫ map f P f' P' g k l h h₀ = g ≫ sectionMap f' P' := by
  apply pullback.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, map_path, sectionMap_path_assoc]
    rw [hι, ← Category.assoc, ← h, Category.assoc]
    exact congrArg (fun q => g ≫ q) (sectionMap_path f' P').symm

end Categorical

section Model

variable [ModelCategory C] {X Y : C} (f : X ⟶ Y) (P : PathObject Y) [P.IsGood]

/-- The whole source projection is trivial fibrational by actual base change. -/
theorem source_trivialFibration [IsFibrant Y] :
    trivialFibrations C (source f P.toPrepathObject) := by
  have hp : trivialFibrations C P.p₀ :=
    ⟨(fibration_iff _).mp inferInstance, (weakEquivalence_iff _).mp inferInstance⟩
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f P.p₀).flip hp

/-- Fibrancy of the original source makes the far endpoint map a genuine fibration. -/
theorem target_fibration [IsFibrant X] :
    fibrations C (target f P.toPrepathObject) := by
  have hp : fibrations C (endpointPair f P.toPrepathObject) :=
    MorphismProperty.of_isPullback (endpointPair_isPullback f P.toPrepathObject).flip
      ((fibration_iff P.p).mp inferInstance)
  let _ : Fibration (endpointPair f P.toPrepathObject) := (fibration_iff _).mpr hp
  have he : target f P.toPrepathObject = endpointPair f P.toPrepathObject ≫ prod.snd :=
    (endpointPair_snd f P.toPrepathObject).symm
  rw [he, ← fibration_iff]
  infer_instance

/-- A weak original arrow gives a trivial-fibrational far endpoint with the original source
retained. -/
theorem target_trivialFibration [IsFibrant X] [IsFibrant Y] [WeakEquivalence f] :
    trivialFibrations C (target f P.toPrepathObject) := by
  let _ : WeakEquivalence (source f P.toPrepathObject) :=
    (weakEquivalence_iff _).mpr (source_trivialFibration f P).2
  let _ : WeakEquivalence (sectionMap f P.toPrepathObject) :=
    weakEquivalence_of_postcomp_of_fac (sectionMap_source f P.toPrepathObject)
  let _ : WeakEquivalence (target f P.toPrepathObject) :=
    weakEquivalence_of_precomp_of_fac (sectionMap_target f P.toPrepathObject)
  exact ⟨target_fibration f P, (weakEquivalence_iff _).mp inferInstance⟩

end Model

end HomotopicalAlgebra.MappingPath
