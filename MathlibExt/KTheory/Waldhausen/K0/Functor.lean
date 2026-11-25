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

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.KTheory.Waldhausen.K0.Basic
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberExactFunctorTransport

/-!
# Functoriality of Waldhausen `K₀` for exact functors

For Quillen exact categories `C` and `D` with their standard Waldhausen
structures `ExactCategory.waldhausenCategory`, an additive exact functor
`F : C ⥤ D` induces an abelian group morphism on Waldhausen `K₀`.

The map is defined by `QuotientAddGroup.map` over
`FreeAbelianGroup.map F.mapSkeleton.obj`, mirroring
`AlgebraicKTheory.K0.map` only where types genuinely match. Weak-equivalence
generators are preserved because standard weak equivalences are isomorphisms
and functors preserve isomorphisms; cofibration-sequence generators are
preserved by `isCofibrationSequence_map`.

## Main definitions
* `WaldhausenKTheory.K0.map`

## Main results
* `WaldhausenKTheory.K0.map_mk`
* `WaldhausenKTheory.K0.map_id`
* `WaldhausenKTheory.K0.map_comp`
* `WaldhausenKTheory.K0.map_eq_of_iso`

Nonclaims: no general Waldhausen-functor class, equivalence wrapper, ring
structure, `S•`, or additivity.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace WaldhausenKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- The abelian group morphism on Waldhausen `K₀` induced by an additive exact
functor between the standard exact-category Waldhausen structures. -/
noncomputable def K0.map (F : C ⥤ D) [F.Additive] [F.IsExact] :
    @K0 C _ _ (ExactCategory.waldhausenCategory C) →+
      @K0 D _ _ (ExactCategory.waldhausenCategory D) :=
  QuotientAddGroup.map _ _ (FreeAbelianGroup.map F.mapSkeleton.obj) (by
    unfold K0Rel
    rw [AddSubgroup.closure_le]
    rintro x hx
    rcases hx with hx | hx
    · obtain ⟨X, Y, f, hf, rfl⟩ := hx
      simp only [AddSubgroup.mem_comap, SetLike.mem_coe, map_sub,
        FreeAbelianGroup.map_of_apply, Functor.mapSkeleton_obj_toSkeleton]
      have hfIso : MorphismProperty.isomorphisms C f := hf
      have hIsIso : IsIso f :=
        (MorphismProperty.isomorphisms.iff f).mp hfIso
      have hIsIsoD : IsIso (F.map f) := inferInstance
      have hfDProp : MorphismProperty.isomorphisms D (F.map f) :=
        (MorphismProperty.isomorphisms.iff _).mpr hIsIsoD
      have hfD : @IsWeakEquivalence D _ _
          (ExactCategory.waldhausenCategory D) _ _ (F.map f) := hfDProp
      apply AddSubgroup.subset_closure
      apply Set.mem_union_left
      exact ⟨F.obj X, F.obj Y, F.map f, hfD, rfl⟩
    · obtain ⟨X, Y, Z, f, g, hSeq, rfl⟩ := hx
      simp only [AddSubgroup.mem_comap, SetLike.mem_coe, map_sub,
        FreeAbelianGroup.map_of_apply, Functor.mapSkeleton_obj_toSkeleton]
      have hSeqD : @IsCofibrationSequence D _ _
          (ExactCategory.waldhausenCategory D) _ _ _ (F.map f) (F.map g) :=
        CategoryTheory.Waldhausen.SConstruction.isCofibrationSequence_map
          F f g hSeq
      apply AddSubgroup.subset_closure
      apply Set.mem_union_right
      exact ⟨F.obj X, F.obj Y, F.obj Z, F.map f, F.map g, hSeqD, rfl⟩)

/-- Generator action for `K0.map`: the class of `X` maps to the class of `F.obj X`. -/
@[simp]
lemma K0.map_mk (F : C ⥤ D) [F.Additive] [F.IsExact] (X : C) :
    K0.map F (@K0.mk C _ _ (ExactCategory.waldhausenCategory C) X) =
      @K0.mk D _ _ (ExactCategory.waldhausenCategory D) (F.obj X) := by
  simp [K0.map, K0.mk, Functor.mapSkeleton_obj_toSkeleton]

/-- Identity law for `K0.map`: the identity functor induces the identity morphism. -/
@[simp]
lemma K0.map_id :
    K0.map (𝟭 C) =
      AddMonoidHom.id (@K0 C _ _ (ExactCategory.waldhausenCategory C)) := by
  apply @K0.hom_ext C _ _ (ExactCategory.waldhausenCategory C)
  intro X
  simp

/-- Composition law for `K0.map`: `F ⋙ G` induces `(K0.map G).comp (K0.map F)`,
preserving functor-composition order. -/
lemma K0.map_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    K0.map (F ⋙ G) =
      (K0.map G).comp (K0.map F) := by
  apply @K0.hom_ext C _ _ (ExactCategory.waldhausenCategory C)
  intro X
  simp

/-- If `F` and `G` are naturally isomorphic additive exact functors, they induce
the same map on Waldhausen `K₀`, since each component is an isomorphism and
hence identifies `K₀`-classes via `K0.mk_eq_of_iso`. -/
theorem K0.map_eq_of_iso {F G : C ⥤ D}
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (e : F ≅ G) : K0.map F = K0.map G := by
  apply @K0.hom_ext C _ _ (ExactCategory.waldhausenCategory C)
  intro X
  simp only [K0.map_mk]
  exact @K0.mk_eq_of_iso D _ _ (ExactCategory.waldhausenCategory D) _ _
    (e.app X)

end WaldhausenKTheory
