/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyDerivedMappingCalculus
import MathlibExt.AlgebraicTopology.SimplicialSpace.VertexRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback
import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Segal spaces and their finite homotopy-pullback comparisons

The original Rezk spines are assembled from their consecutive edges. The
actual chosen inner enrichment sends these finite pushouts to pullbacks.
Under the named Reedy fibrancy condition, the endpoint restrictions are
Kan fibrations, so these are genuine homotopy pullbacks.

Source: Rezk (2001), Section 4.1, equations (4.2) and (4.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

namespace SSet.Rezk

/-- The original consecutive edge inside the outer standard simplex. -/
def segalSpineEdgeMap (n : ℕ) (i : Fin n) : (Δ[1] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.mkOfSucc i)

/-- The image of the original consecutive edge. -/
abbrev segalSpineEdgeSubcomplex (n : ℕ) (i : Fin n) : (Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.range (segalSpineEdgeMap n i)

/-- The first k consecutive edges of the original n-simplex. -/
def spinePrefixSubcomplex (n k : ℕ) (h : k ≤ n) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i : Fin k, segalSpineEdgeSubcomplex n ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- The original outer vertex at the selected finite coordinate. -/
def segalSpineVertexMap (n k : ℕ) (h : k ≤ n) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ ⟨k, by change k < n + 1; omega⟩)

/-- The image of the selected outer vertex. -/
abbrev segalSpineVertexSubcomplex (n k : ℕ) (h : k ≤ n) :
    (Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.range (segalSpineVertexMap n k h)

private theorem edgeMap_apply (n : ℕ) (i : Fin n) {d : ℕ}
    (x : (Δ[1] : SSet.{u}) _⦋d⦌) (j : Fin (d + 1)) :
    (((segalSpineEdgeMap n i).app (op ⦋d⦌) x) j).val = i.val + (x j).val := by
  change ((SimplexCategory.mkOfSucc i).toOrderHom (x j)).val = _
  generalize x j = a
  fin_cases a <;> rfl

private theorem vertexMap_previous (n k : ℕ) (h : k ≤ n) (hk : 1 ≤ k) :
    segalSpineVertexMap.{u} n k h =
      SSet.stdSimplex.δ (0 : Fin 2) ≫
        segalSpineEdgeMap n ⟨k - 1, by omega⟩ := by
  unfold segalSpineVertexMap segalSpineEdgeMap
  change SSet.stdSimplex.map _ =
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp]
  congr 1
  ext j
  fin_cases j
  change k = k - 1 + 1
  omega

private theorem vertexMap_next (n k : ℕ) (h : k + 1 ≤ n) :
    segalSpineVertexMap.{u} n k (by omega) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ segalSpineEdgeMap n ⟨k, by omega⟩ := by
  unfold segalSpineVertexMap segalSpineEdgeMap
  change SSet.stdSimplex.map _ =
    SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp]
  congr 1
  ext j
  fin_cases j
  rfl

private theorem prefix_succ (n k : ℕ) (h : k + 1 ≤ n) :
    spinePrefixSubcomplex.{u} n k (by omega) ⊔ segalSpineEdgeSubcomplex n ⟨k, by omega⟩ =
      spinePrefixSubcomplex n (k + 1) h := by
  ext d x
  simp only [spinePrefixSubcomplex, Subfunctor.max_obj, Set.mem_union,
    Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last k, hi⟩
  · rintro ⟨i, hi⟩
    by_cases hik : i.val < k
    · exact Or.inl ⟨⟨i.val, hik⟩, hi⟩
    · right
      have heq : i = Fin.last k := by
        apply Fin.ext
        dsimp
        omega
      subst i
      exact hi

private theorem vertex_le_prefix (n k : ℕ) (h : k ≤ n) (hk : 1 ≤ k) :
    segalSpineVertexSubcomplex.{u} n k h ≤ spinePrefixSubcomplex n k h := by
  have hle : segalSpineVertexSubcomplex.{u} n k h ≤
      segalSpineEdgeSubcomplex n ⟨k - 1, by omega⟩ := by
    unfold segalSpineVertexSubcomplex
    rw [vertexMap_previous n k h hk, Subcomplex.range_comp]
    exact Subcomplex.image_le_range _ _
  exact hle.trans (le_iSup
    (fun i : Fin k => segalSpineEdgeSubcomplex n ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
    ⟨k - 1, by omega⟩)

private theorem vertex_le_next_edge (n k : ℕ) (h : k + 1 ≤ n) :
    segalSpineVertexSubcomplex.{u} n k (by omega) ≤ segalSpineEdgeSubcomplex n ⟨k, by omega⟩ := by
  unfold segalSpineVertexSubcomplex
  rw [vertexMap_next n k h, Subcomplex.range_comp]
  exact Subcomplex.image_le_range _ _

private theorem prefix_inf_edge (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    spinePrefixSubcomplex.{u} n k (by omega) ⊓ segalSpineEdgeSubcomplex n ⟨k, by omega⟩ =
      segalSpineVertexSubcomplex n k (by omega) := by
  apply le_antisymm
  · intro d x hx
    rcases d with ⟨⟨d⟩⟩
    rcases hx with ⟨hp, he⟩
    simp only [spinePrefixSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion,
      Subfunctor.range_obj] at hp
    obtain ⟨i, y, hy⟩ := hp
    obtain ⟨z, hz⟩ := he
    refine ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0), ?_⟩
    ext j
    have hyv := congrArg (fun a : (Δ[n] : SSet.{u}) _⦋d⦌ => (a j).val) hy
    have hzv := congrArg (fun a : (Δ[n] : SSet.{u}) _⦋d⦌ => (a j).val) hz
    rw [edgeMap_apply] at hyv hzv
    have hyb := (y j).isLt
    have hzb := (z j).isLt
    change k = (x j).val
    dsimp at hyv hzv
    omega
  · exact le_inf (vertex_le_prefix n k (by omega) hk) (vertex_le_next_edge n k h)

private theorem prefix_full (n : ℕ) : spinePrefixSubcomplex.{u} n n le_rfl =
    spineSubcomplex n := rfl

private theorem prefix_one (n : ℕ) (h : 1 ≤ n) :
    spinePrefixSubcomplex.{u} n 1 h = segalSpineEdgeSubcomplex n ⟨0, by omega⟩ := by
  ext d x
  simp only [spinePrefixSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    have heq : i = 0 := Subsingleton.elim _ _
    subst i
    exact hi
  · intro hx
    exact ⟨0, hx⟩

private theorem prefix_isPushout (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    IsPushout
      (Subcomplex.homOfLE (vertex_le_prefix.{u} n k (by omega) hk))
      (Subcomplex.homOfLE (vertex_le_next_edge.{u} n k h))
      (Subcomplex.homOfLE (show spinePrefixSubcomplex.{u} n k (by omega) ≤
          spinePrefixSubcomplex n (k + 1) h from by
        rw [← prefix_succ n k h]
        exact le_sup_left))
      (Subcomplex.homOfLE (show segalSpineEdgeSubcomplex.{u} n ⟨k, by omega⟩ ≤
          spinePrefixSubcomplex n (k + 1) h from by
        rw [← prefix_succ n k h]
        exact le_sup_right)) := by
  exact (show Subcomplex.BicartSq
    (segalSpineVertexSubcomplex.{u} n k (by omega)) (spinePrefixSubcomplex n k (by omega))
    (segalSpineEdgeSubcomplex n ⟨k, by omega⟩) (spinePrefixSubcomplex n (k + 1) h) from
      { sup_eq := prefix_succ n k h
        inf_eq := prefix_inf_edge n k h hk }).isPushout


/-- The original shared vertex enters the finite prefix of consecutive edges. -/
def spinePrefixVertexLeft (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (segalSpineVertexSubcomplex.{u} n k (Nat.le_of_succ_le h) : SSet.{u}) ⟶
      (spinePrefixSubcomplex n k (Nat.le_of_succ_le h) : SSet.{u}) :=
  Subcomplex.homOfLE (vertex_le_prefix n k (Nat.le_of_succ_le h) hk)

/-- The shared vertex is the source vertex of the next consecutive edge. -/
def spinePrefixVertexRight (n k : ℕ) (h : k + 1 ≤ n) :
    (segalSpineVertexSubcomplex.{u} n k (Nat.le_of_succ_le h) : SSet.{u}) ⟶
      (segalSpineEdgeSubcomplex n ⟨k, Nat.lt_of_succ_le h⟩ : SSet.{u}) :=
  Subcomplex.homOfLE (vertex_le_next_edge n k h)

/-- The original finite prefix includes into the prefix with one more edge. -/
def spinePrefixLeft (n k : ℕ) (h : k + 1 ≤ n) :
    (spinePrefixSubcomplex.{u} n k (Nat.le_of_succ_le h) : SSet.{u}) ⟶
      (spinePrefixSubcomplex n (k + 1) h : SSet.{u}) :=
  Subcomplex.homOfLE (by
    rw [← prefix_succ n k h]
    exact le_sup_left)

/-- The new consecutive edge includes into the enlarged finite prefix. -/
def spinePrefixRight (n k : ℕ) (h : k + 1 ≤ n) :
    (segalSpineEdgeSubcomplex.{u} n ⟨k, Nat.lt_of_succ_le h⟩ : SSet.{u}) ⟶
      (spinePrefixSubcomplex n (k + 1) h : SSet.{u}) :=
  Subcomplex.homOfLE (by
    rw [← prefix_succ n k h]
    exact le_sup_right)

instance spinePrefixVertexLeft_mono (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    Mono (spinePrefixVertexLeft.{u} n k h hk) := by
  unfold spinePrefixVertexLeft
  infer_instance

instance spinePrefixVertexRight_mono (n k : ℕ) (h : k + 1 ≤ n) :
    Mono (spinePrefixVertexRight.{u} n k h) := by
  unfold spinePrefixVertexRight
  infer_instance

instance spinePrefixLeft_mono (n k : ℕ) (h : k + 1 ≤ n) :
    Mono (spinePrefixLeft.{u} n k h) := by
  unfold spinePrefixLeft
  infer_instance

instance spinePrefixRight_mono (n k : ℕ) (h : k + 1 ≤ n) :
    Mono (spinePrefixRight.{u} n k h) := by
  unfold spinePrefixRight
  infer_instance

/-- Each original finite spine prefix attaches its next edge at the shared vertex. -/
theorem spinePrefix_isPushout (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    IsPushout (spinePrefixVertexLeft.{u} n k h hk) (spinePrefixVertexRight n k h)
      (spinePrefixLeft n k h) (spinePrefixRight n k h) :=
  prefix_isPushout n k h hk

/-- At the full finite prefix, the object is the original Rezk spine. -/
theorem spinePrefixSubcomplex_full (n : ℕ) :
    spinePrefixSubcomplex.{u} n n le_rfl = spineSubcomplex n :=
  prefix_full n

/-- The first nonempty prefix consists of the original first consecutive edge. -/
theorem spinePrefixSubcomplex_one (n : ℕ) (h : 1 ≤ n) :
    spinePrefixSubcomplex.{u} n 1 h = segalSpineEdgeSubcomplex n ⟨0, Nat.lt_of_succ_le h⟩ :=
  prefix_one n h

instance segalSpineEdgeMap_mono (n : ℕ) (i : Fin n) :
    Mono (segalSpineEdgeMap.{u} n i) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [CategoryTheory.mono_iff_injective]
  intro x y hxy
  rcases d with ⟨⟨d⟩⟩
  ext j
  have h := congrArg (fun a : (Δ[n] : SSet.{u}) _⦋d⦌ => (a j).val) hxy
  rw [edgeMap_apply, edgeMap_apply] at h
  omega

instance segalSpineVertexMap_mono (n k : ℕ) (h : k ≤ n) :
    Mono (segalSpineVertexMap.{u} n k h) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [CategoryTheory.mono_iff_injective]
  intro x y _hxy
  rcases d with ⟨⟨d⟩⟩
  ext j
  have hx : (x j).val < 1 := (x j).isLt
  have hy : (y j).val < 1 := (y j).isLt
  omega

/-- The preceding last consecutive edge includes into the original finite prefix. -/
def spinePrefixPreviousEdge (n k : ℕ) (h : k ≤ n) (hk : 1 ≤ k) :
    (Δ[1] : SSet.{u}) ⟶ (spinePrefixSubcomplex.{u} n k h : SSet.{u}) :=
  (spinePrefixSubcomplex n k h).lift
    (segalSpineEdgeMap n ⟨k - 1, by omega⟩) (by
      unfold spinePrefixSubcomplex
      exact le_iSup (fun j : Fin k => segalSpineEdgeSubcomplex n
        ⟨j.val, lt_of_lt_of_le j.isLt h⟩) ⟨k - 1, by omega⟩)

/-- The first prefix includes the full first edge with its original map. -/
theorem spinePrefixPreviousEdge_one (n : ℕ) (hn : 1 ≤ n) :
    spinePrefixPreviousEdge.{u} n 1 hn le_rfl =
      SSet.Subcomplex.toRange (segalSpineEdgeMap n ⟨0, Nat.lt_of_succ_le hn⟩) ≫
        (SSet.Subcomplex.eqToIso (spinePrefixSubcomplex_one.{u} n hn)).inv := by
  apply (cancel_mono (spinePrefixSubcomplex.{u} n 1 hn).ι).mp
  rw [Category.assoc, SSet.Subcomplex.eqToIso_inv, SSet.Subcomplex.homOfLE_ι,
    SSet.Subcomplex.toRange_ι]
  rfl

/-- The shared vertex on the prefix is the target of its preceding last edge. -/
theorem spinePrefixVertexLeft_previousEdge (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    SSet.Subcomplex.toRange (segalSpineVertexMap.{u} n k (Nat.le_of_succ_le h)) ≫
        spinePrefixVertexLeft n k h hk =
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
        spinePrefixPreviousEdge n k (Nat.le_of_succ_le h) hk := by
  apply (cancel_mono (spinePrefixSubcomplex.{u} n k (Nat.le_of_succ_le h)).ι).mp
  change segalSpineVertexMap.{u} n k (Nat.le_of_succ_le h) =
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      segalSpineEdgeMap n ⟨k - 1, by omega⟩
  exact vertexMap_previous n k (Nat.le_of_succ_le h) hk

/-- The shared vertex on the next edge is its original source vertex. -/
theorem spinePrefixVertexRight_nextEdge (n k : ℕ) (h : k + 1 ≤ n) :
    SSet.Subcomplex.toRange (segalSpineVertexMap.{u} n k (Nat.le_of_succ_le h)) ≫
        spinePrefixVertexRight n k h =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.Subcomplex.toRange (segalSpineEdgeMap n ⟨k, Nat.lt_of_succ_le h⟩) := by
  apply (cancel_mono (segalSpineEdgeSubcomplex.{u} n ⟨k, Nat.lt_of_succ_le h⟩).ι).mp
  change segalSpineVertexMap.{u} n k (Nat.le_of_succ_le h) =
    SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
      segalSpineEdgeMap n ⟨k, Nat.lt_of_succ_le h⟩
  exact vertexMap_next n k h

/-- The original consecutive edge factors through the original Rezk spine. -/
def spineEdgeInclusion (n : ℕ) (i : Fin n) :
    (Δ[1] : SSet.{u}) ⟶ (spineSubcomplex.{u} n : SSet.{u}) :=
  (spineSubcomplex n).lift (segalSpineEdgeMap n i) (by
    unfold spineSubcomplex
    exact le_iSup (fun j : Fin n =>
      SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc j))) i)

/-- The factored edge is the literal original edge in the standard simplex. -/
@[reassoc (attr := simp)]
theorem spineEdgeInclusion_ι (n : ℕ) (i : Fin n) :
    spineEdgeInclusion.{u} n i ≫ (spineSubcomplex.{u} n).ι =
      SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) := rfl

/-- The final eligible prefix is the original spine, with its original outer dimension. -/
theorem spinePrefixSubcomplex_last (n : ℕ) (hn : 2 ≤ n) :
    spinePrefixSubcomplex.{u} n (n - 1 + 1) (by omega) = spineSubcomplex n := by
  simpa only [Nat.sub_add_cancel (show 1 ≤ n from by omega)] using prefix_full.{u} n

private theorem vertex_le_spine (n k : ℕ) (h : k ≤ n) (hn : 1 ≤ n) :
    segalSpineVertexSubcomplex.{u} n k h ≤ spineSubcomplex n := by
  by_cases hk : 1 ≤ k
  · have hp : spinePrefixSubcomplex.{u} n k h ≤ spineSubcomplex n := by
      unfold spinePrefixSubcomplex spineSubcomplex
      apply iSup_le
      intro i
      exact le_iSup (fun j : Fin n =>
        SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc j)))
        ⟨i.val, lt_of_lt_of_le i.isLt h⟩
    exact (vertex_le_prefix n k h hk).trans hp
  · have hk0 : k = 0 := by omega
    subst k
    exact (vertex_le_next_edge n 0 hn).trans
      (le_iSup (fun j : Fin n =>
        SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc j)))
        ⟨0, by omega⟩)

private theorem degeneracy_edge_range_le (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin (n + 1)) :
    SSet.Subcomplex.range
        (SSet.stdSimplex.map (SimplexCategory.mkOfSucc j ≫ SimplexCategory.σ i)) ≤
      spineSubcomplex.{u} n := by
  by_cases hji : j.val < i.val
  · let j' : Fin n := ⟨j.val, by omega⟩
    have hf : SimplexCategory.mkOfSucc j ≫ SimplexCategory.σ i =
        SimplexCategory.mkOfSucc j' := by
      ext a
      fin_cases a
      · change (i.predAbove j.castSucc).val = j'.val
        rw [Fin.predAbove_of_le_castSucc i _ (by change j.val ≤ i.val; omega)]
        rfl
      · change (i.predAbove j.succ).val = j'.val + 1
        rw [Fin.predAbove_of_le_castSucc i _ (by change j.val + 1 ≤ i.val; omega)]
        rfl
    rw [hf]
    exact le_iSup (fun l : Fin n =>
      SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc l))) j'
  · by_cases hij : i.val < j.val
    · let j' : Fin n := ⟨j.val - 1, by omega⟩
      have hf : SimplexCategory.mkOfSucc j ≫ SimplexCategory.σ i =
          SimplexCategory.mkOfSucc j' := by
        ext a
        fin_cases a
        · change (i.predAbove j.castSucc).val = j'.val
          rw [Fin.predAbove_of_castSucc_lt i _ (by change i.val < j.val; exact hij)]
          rfl
        · change (i.predAbove j.succ).val = j'.val + 1
          rw [Fin.predAbove_of_castSucc_lt i _ (by change i.val < j.val + 1; omega)]
          change j.val + 1 - 1 = j.val - 1 + 1
          omega
      rw [hf]
      exact le_iSup (fun l : Fin n =>
        SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc l))) j'
    · have hjiEq : j = i := Fin.ext (by omega)
      subst j
      have hf : SimplexCategory.mkOfSucc i ≫ SimplexCategory.σ i =
          SimplexCategory.const ⦋1⦌ ⦋n⦌ i := by
        ext a
        fin_cases a
        · change (i.predAbove i.castSucc).val = i.val
          rw [Fin.predAbove_of_le_castSucc i _ le_rfl]
          rfl
        · change (i.predAbove i.succ).val = i.val
          rw [Fin.predAbove_of_castSucc_lt i _ Fin.castSucc_lt_succ]
          exact Nat.add_sub_cancel i.val 1
      rw [hf]
      have hfac : SimplexCategory.const ⦋1⦌ ⦋n⦌ i =
          SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ≫
            SimplexCategory.const ⦋0⦌ ⦋n⦌ ⟨i.val, by change i.val < n + 1; exact i.isLt⟩ := by
        ext a
        fin_cases a <;> rfl
      rw [hfac, SSet.stdSimplex.map_comp, SSet.Subcomplex.range_comp]
      exact (SSet.Subcomplex.image_le_range _ _).trans
        (vertex_le_spine n i.val (by omega) hn)

private theorem spine_degeneracy_image_le (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (spineSubcomplex.{u} (n + 1)).image (SSet.stdSimplex.map (SimplexCategory.σ i)) ≤
      spineSubcomplex n := by
  unfold spineSubcomplex
  rw [SSet.Subcomplex.image_iSup]
  apply iSup_le
  intro j
  rw [← SSet.Subcomplex.range_comp, ← SSet.stdSimplex.map_comp]
  exact degeneracy_edge_range_le n hn i j

/-- Every original degeneracy in positive dimension induces the original spine map. -/
def spineDegeneracy (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (spineSubcomplex.{u} (n + 1) : SSet.{u}) ⟶ (spineSubcomplex.{u} n : SSet.{u}) :=
  (spineSubcomplex n).lift
    ((spineSubcomplex (n + 1)).ι ≫ SSet.stdSimplex.map (SimplexCategory.σ i)) (by
      rw [← SSet.Subcomplex.image_eq_range]
      exact spine_degeneracy_image_le n hn i)

/-- The spine degeneracy retains the literal original degeneracy square. -/
@[reassoc (attr := simp)]
theorem spineDegeneracy_ι (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    spineDegeneracy.{u} n hn i ≫ (spineSubcomplex n).ι =
      (spineSubcomplex (n + 1)).ι ≫ SSet.stdSimplex.map (SimplexCategory.σ i) := rfl

end SSet.Rezk

namespace SimplicialSpace

open HomotopicalAlgebra CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner

/-- The Segal-space predicate on the original carrier and named Reedy model. -/
def segalSpaces : ObjectProperty SimplicialSpace.{u} := by
  letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact fun W => IsFibrant W ∧ ∀ n : ℕ, 2 ≤ n →
    SSet.realizationWeakEquivalences
      ((innerHomFunctor.map
        (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W)

/-- The predicate keeps the literal model and every original spine test. -/
theorem segalSpaces_iff (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    segalSpaces W ↔ IsFibrant W ∧ ∀ n : ℕ, 2 ≤ n →
      SSet.realizationWeakEquivalences
        ((innerHomFunctor.map
          (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W) :=
  Iff.rfl




private theorem discrete_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} :=
  ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsColimits _ (fun k => ?_)
    change IsColimit
      ((((evaluation _ _).obj k ⋙ SimplicialObject.const (Type u)).mapCocone c))
    exact isColimitOfPreserves _ hc⟩⟩⟩

private theorem inner_flip_preservesPullbacks (W : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj W) := by
  let : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let : (innerTensor K).IsLeftAdjoint :=
      (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan W

/-- The actual inner enrichment turns every finite spine attachment into a pullback. -/
theorem spinePrefixMapping_isPullback (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    IsPullback
      ((discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft.{u} n k h).op)
      ((discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight.{u} n k h).op)
      ((discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexLeft.{u} n k h hk).op)
      ((discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexRight.{u} n k h).op) := by
  let := discrete_preservesPushouts.{u}
  let := inner_flip_preservesPullbacks W
  have sq := ((SSet.Rezk.spinePrefix_isPushout.{u} n k h hk).map
    SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact (sq.op.map (innerHomFunctor.flip.obj W)).flip

/-- The original finite edge cospan, before any replacement of its base. -/
@[implicit_reducible]
def spinePrefixMappingCospan (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) : WalkingCospan ⥤ SSet.{u} :=
  cospan
    ((discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexLeft.{u} n k h hk).op)
    ((discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexRight.{u} n k h).op)

/-- The whole raw spine mapping object is the chosen strict finite pullback at this step. -/
def spinePrefixMappingIso (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (discreteSourceMapping W).obj
        (op (SSet.Rezk.spinePrefixSubcomplex.{u} n (k + 1) h : SSet.{u})) ≅
      limit (spinePrefixMappingCospan W n k h hk) :=
  (spinePrefixMapping_isPullback W n k h hk).isoPullback


open scoped SSet.modelCategoryQuillen
attribute [local instance] ReedyModel.modelCategory

private theorem discreteSourceMapping_kan (A : SSet.{u}) (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → SSet.KanComplex ((discreteSourceMapping W).obj (op A)) := by
  intro hW
  exact ReedyModel.innerHom_kanComplex
    (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)) W
    (ReedyModel.isCofibrant _) hW

private theorem discreteSourceMapping_fibration {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → Fibration ((discreteSourceMapping W).map i.op) := by
  intro hW
  exact VertexRestriction.discreteRestriction_fibration i W hW

/-- The named functorial homotopy pullback of the original finite edge cospan. -/
abbrev spinePrefixHomotopyPullback (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) : SSet.{u} :=
  (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).obj
    (spinePrefixMappingCospan W n k h hk)

/-- The actual comparison from the strict finite prefix to the named homotopy pullback. -/
def spinePrefixToHomotopyPullback (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (discreteSourceMapping W).obj
        (op (SSet.Rezk.spinePrefixSubcomplex.{u} n (k + 1) h : SSet.{u})) ⟶
      spinePrefixHomotopyPullback W n k h hk :=
  (spinePrefixMappingIso W n k h hk).hom ≫
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
      (spinePrefixMappingCospan W n k h hk)

private theorem spinePrefixHomotopyPullbackComparison_weak
    (W : SimplicialSpace.{u}) (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → WeakEquivalence
      ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
        (spinePrefixMappingCospan W n k h hk)) := by
  intro hW
  let : IsFibrant ((spinePrefixMappingCospan W n k h hk).obj WalkingCospan.one) :=
    discreteSourceMapping_kan _ W hW
  let : IsFibrant ((spinePrefixMappingCospan W n k h hk).obj WalkingCospan.left) :=
    discreteSourceMapping_kan _ W hW
  let : Fibration ((spinePrefixMappingCospan W n k h hk).map WalkingCospan.Hom.inr) :=
    discreteSourceMapping_fibration _ W hW
  exact HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_inr
    (spinePrefixMappingCospan W n k h hk)

/-- Every strict finite prefix computes a genuine homotopy pullback at a Reedy-fibrant target. -/
theorem spinePrefixToHomotopyPullback_weak (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → SSet.realizationWeakEquivalences
      (spinePrefixToHomotopyPullback W n k h hk) := by
  intro hW
  have hIso : SSet.realizationWeakEquivalences (spinePrefixMappingIso W n k h hk).hom :=
    (HomotopicalAlgebra.weakEquivalence_iff (spinePrefixMappingIso W n k h hk).hom).mp
      inferInstance
  have hComparison : SSet.realizationWeakEquivalences
      ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
        (spinePrefixMappingCospan W n k h hk)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp
      (spinePrefixHomotopyPullbackComparison_weak W n k h hk hW)
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hIso hComparison

@[implicit_reducible]
private def spinePrefixIdentityReplacement (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → FibrantCospanReplacement (spinePrefixMappingCospan W n k h hk) := by
  intro hW
  refine
    { P := spinePrefixMappingCospan W n k h hk
      unit := 𝟙 _
      isFibrant_one := discreteSourceMapping_kan _ W hW
      fibration_inl := discreteSourceMapping_fibration _ W hW
      fibration_inr := discreteSourceMapping_fibration _ W hW
      unit_app_mem_trivialCofibrations := ?_ }
  intro j
  exact (mem_trivialCofibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

private theorem spinePrefixIdentityReplacement_fromPullback (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    ∀ hW : IsFibrant W,
      (spinePrefixIdentityReplacement W n k h hk hW).fromPullback =
        𝟙 (limit (spinePrefixMappingCospan W n k h hk)) := by
  intro hW
  change lim.map (𝟙 (spinePrefixMappingCospan W n k h hk)) = _
  exact lim.map_id _

/-- The strict finite-pullback isomorphism keeps the original prefix restriction. -/
theorem spinePrefixMappingIso_hom_left (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (spinePrefixMappingIso W n k h hk).hom ≫
        limit.π (spinePrefixMappingCospan W n k h hk) WalkingCospan.left =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft.{u} n k h).op :=
  (spinePrefixMapping_isPullback W n k h hk).isoPullback_hom_fst

/-- The strict finite-pullback isomorphism keeps the next original edge. -/
theorem spinePrefixMappingIso_hom_right (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (spinePrefixMappingIso W n k h hk).hom ≫
        limit.π (spinePrefixMappingCospan W n k h hk) WalkingCospan.right =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight.{u} n k h).op :=
  (spinePrefixMapping_isPullback W n k h hk).isoPullback_hom_snd

/-- The named homotopy pullback admits a weak comparison to the original strict
finite pullback when the original cospan is already fibrant. The comparison is
existential; no inverse of the replacement unit or functorial retraction is selected. -/
theorem spinePrefixHomotopyPullback_exists_weak_comparison (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∃ r : spinePrefixHomotopyPullback W n k h hk ⟶
        limit (spinePrefixMappingCospan W n k h hk),
      SSet.realizationWeakEquivalences r ∧
        spinePrefixToHomotopyPullback W n k h hk ≫ r =
          (spinePrefixMappingIso W n k h hk).hom := by
  intro hW
  obtain ⟨r, hr, hfac⟩ :=
    (spinePrefixIdentityReplacement W n k h hk hW).exists_weakEquivalence_from_homotopyPullback
  refine ⟨r, (HomotopicalAlgebra.weakEquivalence_iff r).mp hr, ?_⟩
  change (spinePrefixMappingIso W n k h hk).hom ≫
      ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
        (spinePrefixMappingCospan W n k h hk)) ≫ r = _
  rw [hfac, spinePrefixIdentityReplacement_fromPullback W n k h hk hW,
    Category.comp_id]


/-- The original Segal restriction, under the actual enriched-Yoneda source comparison. -/
def rawSegalComparison (W : SimplicialSpace.{u}) (n : ℕ) :
    W.diagram.obj (op ⦋n⦌) ⟶
      (discreteSourceMapping W).obj (op (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u})) :=
  (discreteYonedaIso W n).inv ≫
    (discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} n).ι.op

/-- Enriched Yoneda changes no original Segal weak-equivalence test. -/
theorem rawSegalComparison_weak_iff (W : SimplicialSpace.{u}) (n : ℕ) :
    SSet.realizationWeakEquivalences (rawSegalComparison W n) ↔
      SSet.realizationWeakEquivalences
        ((innerHomFunctor.map
          (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W) := by
  have hIso : SSet.realizationWeakEquivalences (discreteYonedaIso W n).inv :=
    (HomotopicalAlgebra.weakEquivalence_iff (discreteYonedaIso W n).inv).mp inferInstance
  exact SSet.realizationWeakEquivalences.precomp_iff _ _ hIso

/-- The finite original edge cospan for the full n-spine, n at least two. -/
abbrev segalMappingCospan (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    WalkingCospan ⥤ SSet.{u} :=
  spinePrefixMappingCospan W n (n - 1) (by omega) (by omega)

/-- The original full-spine mapping object is the actual finite strict edge pullback. -/
def segalSpineMappingIso (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u})) ≅
      limit (segalMappingCospan W n hn) :=
  (discreteSourceMapping W).mapIso
      (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last.{u} n hn)).op ≪≫
    spinePrefixMappingIso W n (n - 1) (by omega) (by omega)

/-- The original n-simplex comparison to its finite chosen strict edge pullback. -/
def segalStrictComparison (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    W.diagram.obj (op ⦋n⦌) ⟶ limit (segalMappingCospan W n hn) :=
  rawSegalComparison W n ≫ (segalSpineMappingIso W n hn).hom

/-- The named functorial finite homotopy-pullback target for every original n at least two. -/
abbrev segalHomotopyPullback (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) : SSet.{u} :=
  (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).obj (segalMappingCospan W n hn)

/-- The original Segal comparison into the named functorial homotopy pullback. -/
def segalHomotopyComparison (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    W.diagram.obj (op ⦋n⦌) ⟶ segalHomotopyPullback W n hn :=
  segalStrictComparison W n hn ≫
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
      (segalMappingCospan W n hn)

/-- The finite strict edge limit is naturally weak exactly for the original spine restriction. -/
theorem segalStrictComparison_weak_iff (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    SSet.realizationWeakEquivalences (segalStrictComparison W n hn) ↔
      SSet.realizationWeakEquivalences
        ((innerHomFunctor.map
          (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W) := by
  have hIso : SSet.realizationWeakEquivalences (segalSpineMappingIso W n hn).hom :=
    (HomotopicalAlgebra.weakEquivalence_iff (segalSpineMappingIso W n hn).hom).mp
      inferInstance
  exact (SSet.realizationWeakEquivalences.postcomp_iff _ _ hIso).trans
    (rawSegalComparison_weak_iff W n)

/-- At actual named Reedy fibrancy, the chosen finite homotopy comparison is precisely
the original all-degree Segal test. -/
theorem segalHomotopyComparison_weak_iff (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W →
      (SSet.realizationWeakEquivalences (segalHomotopyComparison W n hn) ↔
        SSet.realizationWeakEquivalences
          ((innerHomFunctor.map
            (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W)) := by
  intro hW
  have hComparison : SSet.realizationWeakEquivalences
      ((HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
        (segalMappingCospan W n hn)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp
      (spinePrefixHomotopyPullbackComparison_weak W n (n - 1) (by omega) (by omega) hW)
  exact (SSet.realizationWeakEquivalences.postcomp_iff _ _ hComparison).trans
    (segalStrictComparison_weak_iff W n hn)

/-- Segal spaces are exactly the actual Reedy-fibrant objects whose original finite
homotopy-pullback Segal comparisons are weak in every n at least two. -/
theorem segalSpaces_iff_homotopyPullbackComparisons (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    segalSpaces W ↔ IsFibrant W ∧ ∀ (n : ℕ) (hn : 2 ≤ n),
      SSet.realizationWeakEquivalences (segalHomotopyComparison W n hn) := by
  constructor
  · rintro ⟨hW, hSegal⟩
    exact ⟨hW, fun n hn => (segalHomotopyComparison_weak_iff W n hn hW).mpr (hSegal n hn)⟩
  · rintro ⟨hW, hSegal⟩
    exact ⟨hW, fun n hn => (segalHomotopyComparison_weak_iff W n hn hW).mp (hSegal n hn)⟩


/-- Restriction to every original consecutive edge retains its original outer structure map. -/
theorem rawSegalComparison_edge (W : SimplicialSpace.{u}) (n : ℕ) (i : Fin n) :
    rawSegalComparison W n ≫
        (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion.{u} n i).op ≫
        (discreteYonedaIso W 1).hom =
      W.diagram.map (SimplexCategory.mkOfSucc i).op := by
  unfold rawSegalComparison
  rw [← Category.assoc, Category.assoc (discreteYonedaIso W n).inv,
    ← (discreteSourceMapping W).map_comp, ← op_comp, SSet.Rezk.spineEdgeInclusion_ι]
  rw [Category.assoc, discreteYonedaIso_naturality_index W (SimplexCategory.mkOfSucc i)]
  simp only [Iso.inv_hom_id_assoc]

/-- Each original Segal comparison is a trivial Kan fibration for a Segal space. -/
theorem rawSegalComparison_trivialFibration (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (rawSegalComparison W n) := by
  let : Fibration ((discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} n).ι.op) :=
    discreteSourceMapping_fibration _ W hW.1
  let : Fibration (rawSegalComparison W n) := by
    unfold rawSegalComparison
    infer_instance
  let : WeakEquivalence (rawSegalComparison W n) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      ((rawSegalComparison_weak_iff W n).mpr (hW.2 n hn))
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- The comparison into the original strict finite edge limit is also a trivial Kan fibration. -/
theorem segalStrictComparison_trivialFibration (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (segalStrictComparison W n hn) := by
  obtain ⟨hF, hWeak⟩ :=
    (mem_trivialFibrations_iff _).mp (rawSegalComparison_trivialFibration W n hn hW)
  let : Fibration (rawSegalComparison W n) := hF
  let : WeakEquivalence (rawSegalComparison W n) := hWeak
  unfold segalStrictComparison
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

open scoped SimplicialSpace.ReedyModel

/-- The accepted genuine Reedy calculus preserves the full chosen Q/R precomposition tests. -/
theorem segalSpaces_iff_derivedSpineTests (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    letI : HasFunctorialFactorization (cofibrations SimplicialSpace.{u})
      (trivialFibrations SimplicialSpace.{u}) :=
        ReedyModel.instHasFunctorialFactorizationCofibrationsTrivialFibrations
    letI : HasFunctorialFactorization (trivialCofibrations SimplicialSpace.{u})
      (fibrations SimplicialSpace.{u}) :=
        ReedyModel.instHasFunctorialFactorizationTrivialCofibrationsFibrations
    segalSpaces W ↔ IsFibrant W ∧ ∀ (n : ℕ) (_hn : 2 ≤ n),
      SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := SimplicialSpace.{u})
          (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)) W) := by
  constructor
  · rintro ⟨hW, hSegal⟩
    exact ⟨hW, fun n hn =>
      (ReedyModel.derived_weak_iff_raw_of_isFibrant _ W hW).mpr (hSegal n hn)⟩
  · rintro ⟨hW, hSegal⟩
    exact ⟨hW, fun n hn =>
      (ReedyModel.derived_weak_iff_raw_of_isFibrant _ W hW).mp (hSegal n hn)⟩


/-- Every original simplicial-space arrow acts on the actual discrete-source inner ends. -/
def discreteSourceMappingMap {W W' : SimplicialSpace.{u}} (q : W ⟶ W') :
    discreteSourceMapping W ⟶ discreteSourceMapping W' :=
  Functor.whiskerLeft (SSet.simplicialSpaceDiscrete ⋙ ofSimplicialObject).op
    (innerHomFunctor.flip.map q)

/-- The enriched representable comparison keeps the original target arrow at every outer level. -/
theorem discreteYonedaIso_naturality_target {W W' : SimplicialSpace.{u}}
    (q : W ⟶ W') (n : ℕ) :
    (discreteSourceMappingMap q).app (op (Δ[n] : SSet.{u})) ≫
        (discreteYonedaIso W' n).hom =
      (discreteYonedaIso W n).hom ≫ q.hom.app (op ⦋n⦌) :=
  SSet.Rezk.pointwiseYonedaIso_naturality_target n q.hom

/-- The original arrow acts on all three terms and both legs of the finite edge cospan. -/
def spinePrefixMappingCospanMap {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    spinePrefixMappingCospan W n k h hk ⟶ spinePrefixMappingCospan W' n k h hk :=
  cospanHomMk
    ((discreteSourceMappingMap q).app
      (op (SSet.Rezk.segalSpineVertexSubcomplex.{u} n k (by omega) : SSet.{u})))
    ((discreteSourceMappingMap q).app
      (op (SSet.Rezk.spinePrefixSubcomplex.{u} n k (by omega) : SSet.{u})))
    ((discreteSourceMappingMap q).app
      (op (SSet.Rezk.segalSpineEdgeSubcomplex.{u} n ⟨k, by omega⟩ : SSet.{u})))
    ((discreteSourceMappingMap q).naturality (SSet.Rezk.spinePrefixVertexLeft n k h hk).op)
    ((discreteSourceMappingMap q).naturality (SSet.Rezk.spinePrefixVertexRight n k h).op)

/-- The strict finite comparison is natural for every original simplicial-space arrow. -/
theorem spinePrefixMappingIso_naturality {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (discreteSourceMappingMap q).app
        (op (SSet.Rezk.spinePrefixSubcomplex.{u} n (k + 1) h : SSet.{u})) ≫
        (spinePrefixMappingIso W' n k h hk).hom =
      (spinePrefixMappingIso W n k h hk).hom ≫
        lim.map (spinePrefixMappingCospanMap q n k h hk) := by
  apply (IsPullback.of_isLimit_cone
    (limit.isLimit (spinePrefixMappingCospan W' n k h hk))).hom_ext
  · change ((discreteSourceMappingMap q).app _ ≫ (spinePrefixMappingIso W' n k h hk).hom) ≫
        limit.π (spinePrefixMappingCospan W' n k h hk) WalkingCospan.left =
      ((spinePrefixMappingIso W n k h hk).hom ≫
        lim.map (spinePrefixMappingCospanMap q n k h hk)) ≫
        limit.π (spinePrefixMappingCospan W' n k h hk) WalkingCospan.left
    have hπ : lim.map (spinePrefixMappingCospanMap q n k h hk) ≫
        limit.π (spinePrefixMappingCospan W' n k h hk) WalkingCospan.left =
      limit.π (spinePrefixMappingCospan W n k h hk) WalkingCospan.left ≫
        (spinePrefixMappingCospanMap q n k h hk).app WalkingCospan.left :=
      limMap_π _ _
    rw [Category.assoc, spinePrefixMappingIso_hom_left, Category.assoc, hπ,
      ← Category.assoc, spinePrefixMappingIso_hom_left]
    exact ((discreteSourceMappingMap q).naturality (SSet.Rezk.spinePrefixLeft n k h).op).symm
  · change ((discreteSourceMappingMap q).app _ ≫ (spinePrefixMappingIso W' n k h hk).hom) ≫
        limit.π (spinePrefixMappingCospan W' n k h hk) WalkingCospan.right =
      ((spinePrefixMappingIso W n k h hk).hom ≫
        lim.map (spinePrefixMappingCospanMap q n k h hk)) ≫
        limit.π (spinePrefixMappingCospan W' n k h hk) WalkingCospan.right
    have hπ : lim.map (spinePrefixMappingCospanMap q n k h hk) ≫
        limit.π (spinePrefixMappingCospan W' n k h hk) WalkingCospan.right =
      limit.π (spinePrefixMappingCospan W n k h hk) WalkingCospan.right ≫
        (spinePrefixMappingCospanMap q n k h hk).app WalkingCospan.right :=
      limMap_π _ _
    rw [Category.assoc, spinePrefixMappingIso_hom_right, Category.assoc, hπ,
      ← Category.assoc, spinePrefixMappingIso_hom_right]
    exact ((discreteSourceMappingMap q).naturality (SSet.Rezk.spinePrefixRight n k h).op).symm

/-- The named functorial homotopy-pullback comparison retains the original arrow's naturality. -/
theorem spinePrefixToHomotopyPullback_naturality {W W' : SimplicialSpace.{u}}
    (q : W ⟶ W') (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (discreteSourceMappingMap q).app
        (op (SSet.Rezk.spinePrefixSubcomplex.{u} n (k + 1) h : SSet.{u})) ≫
        spinePrefixToHomotopyPullback W' n k h hk =
      spinePrefixToHomotopyPullback W n k h hk ≫
        (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map
          (spinePrefixMappingCospanMap q n k h hk) := by
  unfold spinePrefixToHomotopyPullback
  rw [← Category.assoc, spinePrefixMappingIso_naturality, Category.assoc]
  rw [(HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).naturality
    (spinePrefixMappingCospanMap q n k h hk)]
  exact (Category.assoc _ _ _).symm


/-- The original target arrow acts on the complete finite Segal edge cospan. -/
abbrev segalMappingCospanMap {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n : ℕ) (hn : 2 ≤ n) : segalMappingCospan W n hn ⟶ segalMappingCospan W' n hn :=
  spinePrefixMappingCospanMap q n (n - 1) (by omega) (by omega)

/-- The full original-spine isomorphism is natural in every original target arrow. -/
theorem segalSpineMappingIso_naturality {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n : ℕ) (hn : 2 ≤ n) :
    (discreteSourceMappingMap q).app (op (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u})) ≫
        (segalSpineMappingIso W' n hn).hom =
      (segalSpineMappingIso W n hn).hom ≫ lim.map (segalMappingCospanMap q n hn) := by
  have hnat := (discreteSourceMappingMap q).naturality
    (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last.{u} n hn)).op.hom
  unfold segalSpineMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← hnat, Category.assoc, spinePrefixMappingIso_naturality]
  exact (Category.assoc _ _ _).symm

/-- The original Segal comparison retains the complete target-arrow naturality equation. -/
theorem rawSegalComparison_naturality {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n : ℕ) :
    rawSegalComparison W n ≫
        (discreteSourceMappingMap q).app (op (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u})) =
      q.hom.app (op ⦋n⦌) ≫ rawSegalComparison W' n := by
  have hInv : q.hom.app (op ⦋n⦌) ≫ (discreteYonedaIso W' n).inv =
      (discreteYonedaIso W n).inv ≫
        (discreteSourceMappingMap q).app (op (Δ[n] : SSet.{u})) := by
    apply (cancel_mono (discreteYonedaIso W' n).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      discreteYonedaIso_naturality_target q n, Iso.inv_hom_id_assoc]
  unfold rawSegalComparison
  rw [Category.assoc, (discreteSourceMappingMap q).naturality
    (SSet.Rezk.spineSubcomplex.{u} n).ι.op, ← Category.assoc, ← hInv]
  exact Category.assoc _ _ _

/-- Naturality of the finite strict Segal comparison keeps the original n-simplex map. -/
theorem segalStrictComparison_naturality {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n : ℕ) (hn : 2 ≤ n) :
    q.hom.app (op ⦋n⦌) ≫ segalStrictComparison W' n hn =
      segalStrictComparison W n hn ≫ lim.map (segalMappingCospanMap q n hn) := by
  unfold segalStrictComparison
  rw [← Category.assoc, ← rawSegalComparison_naturality, Category.assoc,
    segalSpineMappingIso_naturality]
  exact (Category.assoc _ _ _).symm

/-- Naturality of the named functorial homotopy-pullback Segal comparison uses the original
arrow. -/
theorem segalHomotopyComparison_naturality {W W' : SimplicialSpace.{u}} (q : W ⟶ W')
    (n : ℕ) (hn : 2 ≤ n) :
    q.hom.app (op ⦋n⦌) ≫ segalHomotopyComparison W' n hn =
      segalHomotopyComparison W n hn ≫
        (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).map
          (segalMappingCospanMap q n hn) := by
  unfold segalHomotopyComparison
  rw [← Category.assoc, segalStrictComparison_naturality, Category.assoc]
  rw [(HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).naturality
    (segalMappingCospanMap q n hn)]
  exact (Category.assoc _ _ _).symm


/-- The actual projection of the finite strict edge limit to any original consecutive edge. -/
def segalStrictEdgeProjection (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    limit (segalMappingCospan W n hn) ⟶ W.diagram.obj (op ⦋1⦌) :=
  (segalSpineMappingIso W n hn).inv ≫
    (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion.{u} n i).op ≫
    (discreteYonedaIso W 1).hom

/-- Every labelled projection of the strict Segal comparison is the original outer edge map. -/
theorem segalStrictComparison_edge (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    segalStrictComparison W n hn ≫ segalStrictEdgeProjection W n hn i =
      W.diagram.map (SimplexCategory.mkOfSucc i).op := by
  unfold segalStrictComparison segalStrictEdgeProjection
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact rawSegalComparison_edge W n i

/-- At actual Reedy fibrancy, the named homotopy pullback has an existential weak
comparison to the original finite strict edge limit under the full original Segal map. -/
theorem segalHomotopyComparison_exists_weak_comparison (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∃ r : segalHomotopyPullback W n hn ⟶ limit (segalMappingCospan W n hn),
      SSet.realizationWeakEquivalences r ∧
        segalHomotopyComparison W n hn ≫ r = segalStrictComparison W n hn := by
  intro hW
  obtain ⟨r, hr, hfac⟩ := spinePrefixHomotopyPullback_exists_weak_comparison
    W n (n - 1) (by omega) (by omega) hW
  refine ⟨r, hr, ?_⟩
  have h := congrArg (fun f => rawSegalComparison W n ≫
    ((discreteSourceMapping W).mapIso
      (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last.{u} n hn)).op).hom ≫ f)
    hfac
  simpa only [segalHomotopyComparison, segalStrictComparison, segalSpineMappingIso,
    Iso.trans_hom, spinePrefixToHomotopyPullback, Category.assoc] using h

/-- The weak comparison preserves all n original edge projections simultaneously. -/
theorem segalHomotopyComparison_exists_weak_edgeComparison (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∃ r : segalHomotopyPullback W n hn ⟶ limit (segalMappingCospan W n hn),
      SSet.realizationWeakEquivalences r ∧ ∀ i : Fin n,
        segalHomotopyComparison W n hn ≫ r ≫ segalStrictEdgeProjection W n hn i =
          W.diagram.map (SimplexCategory.mkOfSucc i).op := by
  intro hW
  obtain ⟨r, hr, hfac⟩ := segalHomotopyComparison_exists_weak_comparison W n hn hW
  refine ⟨r, hr, fun i => ?_⟩
  rw [← Category.assoc, hfac, segalStrictComparison_edge]


/-- The inverse enriched-Yoneda map retains every original index operator. -/
theorem discreteYonedaIso_inv_naturality_index (W : SimplicialSpace.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    (discreteYonedaIso W n).inv ≫ (discreteSourceMapping W).map (SSet.stdSimplex.map f).op =
      W.diagram.map f.op ≫ (discreteYonedaIso W m).inv := by
  apply (cancel_mono (discreteYonedaIso W m).hom).mp
  rw [Category.assoc, discreteYonedaIso_naturality_index, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every positive-dimensional original degeneracy commutes with the literal spine comparison. -/
theorem rawSegalComparison_degeneracy (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    rawSegalComparison W n ≫
        (discreteSourceMapping W).map (SSet.Rezk.spineDegeneracy.{u} n hn i).op =
      W.diagram.map (SimplexCategory.σ i).op ≫ rawSegalComparison W (n + 1) := by
  unfold rawSegalComparison
  rw [Category.assoc, ← (discreteSourceMapping W).map_comp,
    ← op_comp, SSet.Rezk.spineDegeneracy_ι, op_comp, (discreteSourceMapping W).map_comp,
    ← Category.assoc, discreteYonedaIso_inv_naturality_index]
  exact Category.assoc _ _ _

/-- The original finite degeneracy action on the actual strict edge limits. -/
def segalStrictDegeneracy (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) (i : Fin (n + 1)) :
    limit (segalMappingCospan W n hn) ⟶ limit (segalMappingCospan W (n + 1) (by omega)) :=
  (segalSpineMappingIso W n hn).inv ≫
    (discreteSourceMapping W).map (SSet.Rezk.spineDegeneracy.{u} n (by omega) i).op ≫
    (segalSpineMappingIso W (n + 1) (by omega)).hom

/-- The finite strict Segal comparison retains each original degeneracy, including the last one. -/
theorem segalStrictComparison_degeneracy (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) (i : Fin (n + 1)) :
    segalStrictComparison W n hn ≫ segalStrictDegeneracy W n hn i =
      W.diagram.map (SimplexCategory.σ i).op ≫
        segalStrictComparison W (n + 1) (by omega) := by
  unfold segalStrictComparison segalStrictDegeneracy
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, rawSegalComparison_degeneracy]
  exact Category.assoc _ _ _

/-- At actual Reedy fibrancy, the original degeneracy admits a comparison of the
named homotopy-pullback targets preserving the exact original Segal square.
Only existence is asserted for this index-changing comparison. -/
theorem segalHomotopyComparison_degeneracy_exists (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) (i : Fin (n + 1)) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∃ d : segalHomotopyPullback W n hn ⟶
        segalHomotopyPullback W (n + 1) (by omega),
      segalHomotopyComparison W n hn ≫ d =
        W.diagram.map (SimplexCategory.σ i).op ≫
          segalHomotopyComparison W (n + 1) (by omega) := by
  intro hW
  obtain ⟨r, _hr, hfac⟩ := segalHomotopyComparison_exists_weak_comparison W n hn hW
  refine ⟨r ≫ segalStrictDegeneracy W n hn i ≫
    (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
      (segalMappingCospan W (n + 1) (by omega)), ?_⟩
  rw [← Category.assoc, ← Category.assoc, hfac, segalStrictComparison_degeneracy,
    Category.assoc]
  rfl


/-- The mapping object of an original edge image is the actual outer level W₁. -/
def spineEdgeMappingIso (W : SimplicialSpace.{u}) (n : ℕ) (i : Fin n) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.segalSpineEdgeSubcomplex.{u} n i : SSet.{u})) ≅
      W.diagram.obj (op ⦋1⦌) :=
  (discreteSourceMapping W).mapIso (asIso
    (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap.{u} n i))).op ≪≫
    discreteYonedaIso W 1

/-- The mapping object of an original vertex image is the actual outer level W₀. -/
def spineVertexMappingIso (W : SimplicialSpace.{u}) (n k : ℕ) (h : k ≤ n) :
    (discreteSourceMapping W).obj
        (op (SSet.Rezk.segalSpineVertexSubcomplex.{u} n k h : SSet.{u})) ≅
      W.diagram.obj (op ⦋0⦌) :=
  (discreteSourceMapping W).mapIso (asIso
    (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineVertexMap.{u} n k h))).op ≪≫
    discreteYonedaIso W 0

/-- The prefix's last-edge projection keeps its original consecutive-edge inclusion. -/
def spinePrefixLastEdgeProjection (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k ≤ n) (hk : 1 ≤ k) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.spinePrefixSubcomplex.{u} n k h : SSet.{u})) ⟶
      W.diagram.obj (op ⦋1⦌) :=
  (discreteSourceMapping W).map (SSet.Rezk.spinePrefixPreviousEdge.{u} n k h hk).op ≫
    (discreteYonedaIso W 1).hom


/-- Under the actual vertex and edge Yoneda maps, the right leg is the original d₁ source map. -/
theorem spinePrefixMappingCospan_right (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) :
    (discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexRight.{u} n k h).op ≫
        (spineVertexMappingIso W n k (Nat.le_of_succ_le h)).hom =
      (spineEdgeMappingIso W n ⟨k, Nat.lt_of_succ_le h⟩).hom ≫
        W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op := by
  change (discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexRight.{u} n k h).op ≫
      (discreteSourceMapping W).map
        (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineVertexMap n k (Nat.le_of_succ_le h))).op ≫
      (discreteYonedaIso W 0).hom =
    ((discreteSourceMapping W).map (SSet.Subcomplex.toRange
      (SSet.Rezk.segalSpineEdgeMap n ⟨k, Nat.lt_of_succ_le h⟩)).op ≫
      (discreteYonedaIso W 1).hom) ≫ W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op
  rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp,
    SSet.Rezk.spinePrefixVertexRight_nextEdge, op_comp, (discreteSourceMapping W).map_comp,
    Category.assoc, discreteYonedaIso_naturality_index]
  exact (Category.assoc _ _ _).symm

/-- The prefix leg is the original d₀ target of its preceding last consecutive edge. -/
theorem spinePrefixMappingCospan_left (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    (discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexLeft.{u} n k h hk).op ≫
        (spineVertexMappingIso W n k (Nat.le_of_succ_le h)).hom =
      spinePrefixLastEdgeProjection W n k (Nat.le_of_succ_le h) hk ≫
        W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op := by
  change (discreteSourceMapping W).map (SSet.Rezk.spinePrefixVertexLeft.{u} n k h hk).op ≫
      (discreteSourceMapping W).map
        (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineVertexMap n k (Nat.le_of_succ_le h))).op ≫
      (discreteYonedaIso W 0).hom =
    ((discreteSourceMapping W).map
      (SSet.Rezk.spinePrefixPreviousEdge n k (Nat.le_of_succ_le h) hk).op ≫
      (discreteYonedaIso W 1).hom) ≫ W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op
  rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp,
    SSet.Rezk.spinePrefixVertexLeft_previousEdge, op_comp, (discreteSourceMapping W).map_comp,
    Category.assoc, discreteYonedaIso_naturality_index]
  exact (Category.assoc _ _ _).symm

/-- The finite Segal cospan on the actual W₀/W₁ objects and original d₀/d₁ maps. -/
@[implicit_reducible]
def spinePrefixNativeCospan (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) : WalkingCospan ⥤ SSet.{u} :=
  cospan (spinePrefixLastEdgeProjection W n k (Nat.le_of_succ_le h) hk ≫
    W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op)
    (W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op)

/-- The finite edge/vertex mapping cospan is the genuine native Segal cospan. -/
def spinePrefixMappingCospanIso (W : SimplicialSpace.{u})
    (n k : ℕ) (h : k + 1 ≤ n) (hk : 1 ≤ k) :
    spinePrefixMappingCospan W n k h hk ≅ spinePrefixNativeCospan W n k h hk :=
  cospanIsoMk (spineVertexMappingIso W n k (Nat.le_of_succ_le h)) (Iso.refl _)
    (spineEdgeMappingIso W n ⟨k, Nat.lt_of_succ_le h⟩)
    (by exact (spinePrefixMappingCospan_left W n k h hk).trans (Category.id_comp _).symm)
    (spinePrefixMappingCospan_right W n k h)


/-- The first nonempty prefix mapping object is its actual W₁ object. -/
def spinePrefixFirstMappingIso (W : SimplicialSpace.{u}) (n : ℕ) (hn : 1 ≤ n) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.spinePrefixSubcomplex.{u} n 1 hn : SSet.{u})) ≅
      W.diagram.obj (op ⦋1⦌) :=
  ((discreteSourceMapping W).mapIso
    (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_one.{u} n hn)).op).symm ≪≫
    spineEdgeMappingIso W n ⟨0, Nat.lt_of_succ_le hn⟩

/-- The actual chosen finite Segal homotopy pullback with original W₀/W₁ cospan terms. -/
abbrev segalNativeHomotopyPullback (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) : SSet.{u} :=
  (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).obj
    (spinePrefixNativeCospan W n (n - 1) (by omega) (by omega))

/-- The named mapping-cospan homotopy pullback is canonically the native finite Segal one. -/
def segalHomotopyPullbackNativeIso (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    segalHomotopyPullback W n hn ≅ segalNativeHomotopyPullback W n hn :=
  (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).mapIso
    (spinePrefixMappingCospanIso W n (n - 1) (by omega) (by omega))

/-- The original n-simplex map into its genuine finite chosen Segal homotopy pullback. -/
def segalNativeHomotopyComparison (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    W.diagram.obj (op ⦋n⦌) ⟶ segalNativeHomotopyPullback W n hn :=
  segalHomotopyComparison W n hn ≫ (segalHomotopyPullbackNativeIso W n hn).hom

/-- The native W₀/W₁ finite chosen comparison is weak exactly for the original spine test. -/
theorem segalNativeHomotopyComparison_weak_iff (W : SimplicialSpace.{u})
    (n : ℕ) (hn : 2 ≤ n) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W →
      (SSet.realizationWeakEquivalences (segalNativeHomotopyComparison W n hn) ↔
        SSet.realizationWeakEquivalences
          ((innerHomFunctor.map
            (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W)) := by
  intro hW
  have hIso : SSet.realizationWeakEquivalences (segalHomotopyPullbackNativeIso W n hn).hom :=
    (HomotopicalAlgebra.weakEquivalence_iff (segalHomotopyPullbackNativeIso W n hn).hom).mp
      inferInstance
  exact (SSet.realizationWeakEquivalences.postcomp_iff _ _ hIso).trans
    (segalHomotopyComparison_weak_iff W n hn hW)

/-- The full Segal predicate is equivalent to every genuine chosen finite Segal homotopy test. -/
theorem segalSpaces_iff_nativeHomotopyPullbackComparisons (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    segalSpaces W ↔ IsFibrant W ∧ ∀ (n : ℕ) (hn : 2 ≤ n),
      SSet.realizationWeakEquivalences (segalNativeHomotopyComparison W n hn) := by
  constructor
  · rintro ⟨hW, hSegal⟩
    exact ⟨hW, fun n hn => (segalNativeHomotopyComparison_weak_iff W n hn hW).mpr (hSegal n hn)⟩
  · rintro ⟨hW, hSegal⟩
    exact ⟨hW, fun n hn => (segalNativeHomotopyComparison_weak_iff W n hn hW).mp (hSegal n hn)⟩


/-- The first-prefix Yoneda isomorphism is exactly its original last-edge projection. -/
theorem spinePrefixFirstMappingIso_hom (W : SimplicialSpace.{u}) (n : ℕ) (hn : 1 ≤ n) :
    (spinePrefixFirstMappingIso W n hn).hom =
      spinePrefixLastEdgeProjection W n 1 hn le_rfl := by
  change (discreteSourceMapping W).map
      (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_one.{u} n hn)).inv.op ≫
      (discreteSourceMapping W).map
        (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap n ⟨0, Nat.lt_of_succ_le hn⟩)).op ≫
      (discreteYonedaIso W 1).hom = _
  rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp,
    ← SSet.Rezk.spinePrefixPreviousEdge_one]
  rfl

/-- In degree two the finite Segal cospan is literally W₁ → W₀ ← W₁, ordered d₀ then d₁. -/
def segalTwoMappingCospanIso (W : SimplicialSpace.{u}) :
    segalMappingCospan W 2 (by decide) ≅
      cospan (W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op)
        (W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op) :=
  cospanIsoMk (spineVertexMappingIso W 2 1 (by decide))
    (spinePrefixFirstMappingIso W 2 (by decide))
    (spineEdgeMappingIso W 2 (1 : Fin 2))
    (by
      have h := spinePrefixMappingCospan_left W 2 1 (by decide) (by decide)
      rw [← spinePrefixFirstMappingIso_hom] at h
      exact h)
    (spinePrefixMappingCospan_right W 2 1 (by decide))

/-- The actual named homotopy pullback of the two original W₁ endpoint maps. -/
abbrev segalTwoHomotopyPullback (W : SimplicialSpace.{u}) : SSet.{u} :=
  (HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).obj
    (cospan (W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op)
      (W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op))

/-- The original two-simplex map to its genuine chosen two-edge homotopy pullback. -/
def segalTwoHomotopyComparison (W : SimplicialSpace.{u}) :
    W.diagram.obj (op ⦋2⦌) ⟶ segalTwoHomotopyPullback W :=
  segalHomotopyComparison W 2 (by decide) ≫
    ((HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).mapIso
      (segalTwoMappingCospanIso W)).hom

/-- The literal two-edge chosen homotopy comparison is exactly the original n=2 Segal test. -/
theorem segalTwoHomotopyComparison_weak_iff (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W →
      (SSet.realizationWeakEquivalences (segalTwoHomotopyComparison W) ↔
        SSet.realizationWeakEquivalences
          ((innerHomFunctor.map
            (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} 2)).op).app W)) := by
  intro hW
  have hIso : SSet.realizationWeakEquivalences
      ((HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).mapIso
        (segalTwoMappingCospanIso W)).hom :=
    (HomotopicalAlgebra.weakEquivalence_iff
      ((HomotopicalAlgebra.homotopyPullback (C := SSet.{u})).mapIso
        (segalTwoMappingCospanIso W)).hom).mp inferInstance
  exact (SSet.realizationWeakEquivalences.postcomp_iff _ _ hIso).trans
    (segalHomotopyComparison_weak_iff W 2 (by decide) hW)

end SimplicialSpace
