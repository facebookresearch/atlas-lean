/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-
Provenance: factored out of
`MathlibExt.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank` (2026
development by @junekim623 with Muse), consolidating the copies previously in
`Sheaf/LocallyFree.lean` (`coversTop_prod`, `coversTopProd`) and
`Sheaf/LocallyFreeRank.lean` (`CoversTop.prod`), which now retarget here.
No other copies remain in this layer.
-/

/-!
# Product covers, slice covers and finite sieve intersections

Let J be a Grothendieck topology on C. An object family X_i covers the top
when, for every Z, the arrows T → Z whose domains admit a map T → X_i
for some i form a J-covering sieve.

If C has binary products, two such families X_i,Y_j give the covering
family X_i×Y_j. A top-covering family also gives a cover of each slice
over X₀ by all objects Z → X₀ equipped with a map Z → X_i.
The canonical iterated-slice equivalence transports top covers between
the corresponding slice topologies. Finite intersections of covering
sieves are covering, and membership in such an intersection implies
membership in every factor.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace CategoryTheory.GrothendieckTopology.CoversTop

/-- For a Grothendieck topology J on a category C with binary products,
if the object families X_i and Y_j each cover the top, then the family
of all products X_i×Y_j, indexed by I×J′, covers the top as well. -/
theorem prod {I I' : Type*} {X : I → C} {Y : I' → C} [HasBinaryProducts C]
    (hX : J.CoversTop X) (hY : J.CoversTop Y) :
    J.CoversTop (fun p : I × I' ↦ X p.1 ⨯ Y p.2) := by
  intro Z
  refine J.transitive (hX Z) _ fun T a ha ↦ ?_
  rw [_root_.CategoryTheory.Sieve.mem_ofObjects_iff] at ha
  obtain ⟨i, ⟨a₀⟩⟩ := ha
  refine J.superset_covering ?_ (hY T)
  intro W b hb
  rw [_root_.CategoryTheory.Sieve.mem_ofObjects_iff] at hb
  obtain ⟨j, ⟨k⟩⟩ := hb
  change (_root_.CategoryTheory.Sieve.ofObjects _ Z) (b ≫ a)
  rw [_root_.CategoryTheory.Sieve.mem_ofObjects_iff]
  exact ⟨(i, j), ⟨prod.lift (b ≫ a₀) k⟩⟩

/-- Let J be a Grothendieck topology on C and X_i a top-covering object
family. For every X₀ in C, the slice topology J/X₀ has a top cover
consisting of all objects Z → X₀ equipped with some map Z → X_i. -/
theorem overComma {I : Type*} {X : I → C}
    (hX : J.CoversTop X) (X₀ : C) :
    (J.over X₀).CoversTop
      (fun p : (i : I) × (Z : C) × (Z ⟶ X i) × (Z ⟶ X₀) ↦
        (_root_.CategoryTheory.Over.mk p.2.2.2 : Over X₀)) := by
  intro W
  rw [_root_.CategoryTheory.GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (hX W.left)
  intro Z f hf
  rw [_root_.CategoryTheory.Sieve.mem_ofObjects_iff] at hf
  rw [_root_.CategoryTheory.Sieve.overEquiv_iff, _root_.CategoryTheory.Sieve.mem_ofObjects_iff]
  obtain ⟨i, ⟨a⟩⟩ := hf
  exact ⟨⟨i, Z, a, f ≫ W.hom⟩, ⟨𝟙 _⟩⟩

/-- Let J be a Grothendieck topology on C, X an object and U an object
of C/X. A top cover Y_i of C/U.left for J/U.left is sent by the
inverse canonical equivalence C/U.left ≃ (C/X)/U to a top cover
for the iterated slice topology (J/X)/U. -/
theorem iteratedSliceEquiv_inverse {X : C} (U : Over X) {I : Type*}
    {Y : I → Over U.left} (hY : (J.over U.left).CoversTop Y) :
    ((J.over X).over U).CoversTop
      (fun i => (Over.iteratedSliceEquiv U).inverse.obj (Y i)) := by
  intro W
  have hs := hY ((Over.iteratedSliceEquiv U).functor.obj W)
  have hp : (Sieve.ofObjects Y
        ((Over.iteratedSliceEquiv U).functor.obj W)).functorPushforward
        (Over.iteratedSliceEquiv U).inverse ∈
      ((J.over X).over U)
        ((Over.iteratedSliceEquiv U).inverse.obj
          ((Over.iteratedSliceEquiv U).functor.obj W)) :=
    (Functor.functorPushforward_mem_iff (J.over U.left)
      ((J.over X).over U) (Over.iteratedSliceEquiv U).inverse).mpr hs
  have hle : (Sieve.ofObjects Y
        ((Over.iteratedSliceEquiv U).functor.obj W)).functorPushforward
        (Over.iteratedSliceEquiv U).inverse ≤
      Sieve.ofObjects (fun i => (Over.iteratedSliceEquiv U).inverse.obj (Y i))
        ((Over.iteratedSliceEquiv U).inverse.obj
          ((Over.iteratedSliceEquiv U).functor.obj W)) :=
    Sieve.functorPushforward_ofObjects_le _ _ _
  have hc := ((J.over X).over U).superset_covering hle hp
  have eW := (Over.iteratedSliceEquiv U).symm.counitIso.app W
  have hpb : (Sieve.ofObjects
        (fun i => (Over.iteratedSliceEquiv U).inverse.obj (Y i))
        ((Over.iteratedSliceEquiv U).inverse.obj
          ((Over.iteratedSliceEquiv U).functor.obj W))).pullback
        eW.symm.hom =
      Sieve.ofObjects (fun i => (Over.iteratedSliceEquiv U).inverse.obj (Y i)) W :=
    Sieve.pullback_ofObjects _ eW.symm.hom
  rw [← hpb]
  exact ((J.over X).over U).pullback_stable _ hc

end CategoryTheory.GrothendieckTopology.CoversTop

namespace CategoryTheory.GrothendieckTopology

/-- For a Grothendieck topology K on D and a finite-indexed family T_i
of K-covering sieves on Z, the intersection ⋂ᵢT_i is K-covering. -/
theorem finsetInf_mem {D : Type u} [Category.{v} D]
    {K : GrothendieckTopology D} {Z : D} {ι : Type*} [Fintype ι]
    (T : ι → Sieve Z) (h : ∀ k, T k ∈ K Z) :
    (Finset.univ.inf T) ∈ K Z :=
  Finset.inf_induction (K.top_mem Z)
    (fun _ h₁ _ h₂ => K.intersection_covering h₁ h₂) (fun k _ => h k)

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sieve

/-- In a category D, for a finite-indexed family T_i of sieves on Z,
an arrow h:V → Z belonging to ⋂ᵢT_i belongs to T_k for every
index k. -/
theorem finsetInf_arrows {D : Type u} [Category.{v} D]
    {Z V : D} {ι : Type*} [Fintype ι] (T : ι → Sieve Z)
    (h : V ⟶ Z)
    (hh : (Finset.univ.inf T).arrows h) (k : ι) : (T k).arrows h :=
  (Finset.inf_le (Finset.mem_univ k) : Finset.univ.inf T ≤ T k) _ hh

end CategoryTheory.Sieve

end
