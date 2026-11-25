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

/-!
# Product and comma covers for `GrothendieckTopology.CoversTop`

Two pure site-combinatorics cover refinements shared by the locally-free
sheaf APIs:

* `CategoryTheory.GrothendieckTopology.CoversTop.prod`: the product family
  of two covers covers the top (common refinement of the covers witnessing
  local freeness of two modules).
* `CategoryTheory.GrothendieckTopology.CoversTop.overComma`: a global cover
  induces a cover of every slice via comma objects (no pullbacks needed).
* `CategoryTheory.GrothendieckTopology.CoversTop.iteratedSliceEquiv_inverse`:
  transport of a cover along the inverse of `Over.iteratedSliceEquiv`
  between the two slice topologies (shared by the coherent finiteness
  proofs in `Sheaf/Coherent.lean`).

Two pure sieve-combinatorics lemmas used for the finite-intersection
covers in coherent finiteness proofs:

* `CategoryTheory.GrothendieckTopology.finsetInf_mem`: finite
  intersections of covering sieves cover.
* `CategoryTheory.Sieve.finsetInf_arrows`: membership in a finite
  sieve intersection implies membership in each factor.

Both carry minimal hypotheses (only the site, its topology, and
`HasBinaryProducts` for `prod`).

Provenance: factored out of
`MathlibExt.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank` (2026
development by @junekim623 with Muse), consolidating the copies previously in
`Sheaf/LocallyFree.lean` (`coversTop_prod`, `coversTopProd`) and
`Sheaf/LocallyFreeRank.lean` (`CoversTop.prod`), which now retarget here.
No other copies remain in this layer.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace CategoryTheory.GrothendieckTopology.CoversTop

/-- The product family of two covers is a cover: given `T` mapping to
some `X i`, the pullback sieve contains the `Y`-cover via `prod.lift`. -/
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

/-- A global cover induces a cover of every slice via comma objects:
over `X₀`, take all spans `Z → X i` equipped with a structure map
`Z → X₀`. No pullbacks are needed since `Sieve.ofObjects` only sees
domains. -/
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

/-- Transport a `CoversTop` cover along the inverse of the iterated-slice
equivalence: a cover of `Over U.left` for `J.over U.left` maps to a cover
of `Over U` for `(J.over X).over U` under
`(Over.iteratedSliceEquiv U).inverse`, using that this inverse is a dense
subsite for the two slice topologies. -/
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

/-- Finite intersections of covering sieves are covering. -/
theorem finsetInf_mem {D : Type u} [Category.{v} D]
    {K : GrothendieckTopology D} {Z : D} {ι : Type*} [Fintype ι]
    (T : ι → Sieve Z) (h : ∀ k, T k ∈ K Z) :
    (Finset.univ.inf T) ∈ K Z :=
  Finset.inf_induction (K.top_mem Z)
    (fun _ h₁ _ h₂ => K.intersection_covering h₁ h₂) (fun k _ => h k)

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sieve

/-- Membership in a finite intersection of sieves implies membership in each. -/
theorem finsetInf_arrows {D : Type u} [Category.{v} D]
    {Z V : D} {ι : Type*} [Fintype ι] (T : ι → Sieve Z)
    (h : V ⟶ Z)
    (hh : (Finset.univ.inf T).arrows h) (k : ι) : (T k).arrows h :=
  (Finset.inf_le (Finset.mem_univ k) : Finset.univ.inf T ≤ T k) _ hh

end CategoryTheory.Sieve

end
