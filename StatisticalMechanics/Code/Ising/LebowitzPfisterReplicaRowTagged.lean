/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaFourFunctions












open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

abbrev LPReplicaRowTag := Bool × Bool

def lpReplicaRowCopies (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) : Finset (Copy (lpReplicaCurrentGraph G sites) m) :=
  Finset.univ.filter (fun c => (tag c).1 = row)

def lpReplicaCurrentCopies (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    Finset (Copy (lpReplicaCurrentGraph G sites) m) :=
  Finset.univ.filter (fun c => tag c = (row, current))

section Reflection

variable [Fintype I] [DecidableEq I]



def lpReplicaReflectTag (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Copy (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) ->
      LPReplicaRowTag :=
  fun c => tag ((lpReplicaReflectCopyEquiv G sites m).symm c)

theorem lpReplicaRowCopies_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectTag G sites m tag) row =
      lpReplicaReflectCopies G sites m
        (lpReplicaRowCopies G sites m tag row) := by
  ext c
  simp [lpReplicaRowCopies, lpReplicaReflectTag]

theorem lpReplicaCurrentCopies_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectTag G sites m tag) row current =
      lpReplicaReflectCopies G sites m
        (lpReplicaCurrentCopies G sites m tag row current) := by
  ext c
  simp [lpReplicaCurrentCopies, lpReplicaReflectTag]

theorem lpReplicaCurrentSources_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaCurrentCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row current) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaCurrentCopies G sites m tag row current)).map
          lpReplicaCurrentReflect.toEmbedding := by
  rw [lpReplicaCurrentCopies_reflectTag,
    lpReplicaReflectCopies_sources]

theorem lpReplicaRowConn_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (a b : LPReplicaCurrentVertex V) :
    RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaRowCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row)
        (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔
      RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag row) a b := by
  rw [lpReplicaRowCopies_reflectTag]
  exact lpReplicaReflectCopies_connK G sites m _ a b

end Reflection

section CollisionTag

variable [Fintype I] [DecidableEq I]




def lpReplicaCollisionRowTag
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites a b) -> LPReplicaRowTag :=
  fun c =>
    if c ∈ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) then
      (false, if c ∈ Sa.map
        (lpReplicaCollisionLeftCopyEmbedding G sites a b) then false else true)
    else
      (true, if c ∈ Sb.map
        (lpReplicaCollisionRightCopyEmbedding G sites a b) then false else true)

theorem lpReplicaCollision_origin_disjoint
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Disjoint
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b))
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b)) := by
  rw [Finset.disjoint_left]
  intro c hcL hcR
  simp only [Finset.mem_map, Finset.mem_univ, true_and] at hcL hcR
  rcases hcL with ⟨l, rfl⟩
  rcases hcR with ⟨r, hr⟩
  have h := (lpReplicaCollisionCopyEquiv G sites a b).injective hr
  have hk := congrArg (fun z : LPReplicaCollisionCopy G sites a b =>
    match z.2 with
    | .inl _ => false
    | .inr _ => true) h
  simp at hk

theorem lpReplicaCollision_origin_union
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) ∪
      (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro c
  generalize ho : (lpReplicaCollisionCopyEquiv G sites a b).symm c = o
  rcases o with ⟨e, k | k⟩
  · apply Finset.mem_union_left
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    refine ⟨⟨e, k⟩, ?_⟩
    change lpReplicaCollisionCopyEquiv G sites a b ⟨e, Sum.inl k⟩ = c
    rw [← ho, (lpReplicaCollisionCopyEquiv G sites a b).apply_symm_apply]
  · apply Finset.mem_union_right
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    let cr : Copy (lpReplicaCurrentGraph G sites)
        (fun f => b (lpReplicaCurrentEdgeReflect G sites f)) := ⟨e, k⟩
    let r := (lpReplicaReflectCopyEquiv G sites b).symm cr
    refine ⟨r, ?_⟩
    change lpReplicaCollisionCopyEquiv G sites a b
        ⟨(lpReplicaReflectCopyEquiv G sites b r).1,
          Sum.inr (lpReplicaReflectCopyEquiv G sites b r).2⟩ = c
    rw [(lpReplicaReflectCopyEquiv G sites b).apply_symm_apply cr]
    rw [← ho, (lpReplicaCollisionCopyEquiv G sites a b).apply_symm_apply]

theorem lpReplicaCollision_rightOrigin_eq_sdiff
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) =
      Finset.univ \ ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b)) := by
  apply Finset.Subset.antisymm
  · intro c hc
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      (Finset.disjoint_left.mp
        (lpReplicaCollision_origin_disjoint G sites a b).symm) hc⟩
  · intro c hc
    have hU := Finset.mem_union.mp
      (show c ∈
        (Finset.univ : Finset
          (Copy (lpReplicaCurrentGraph G sites) a)).map
            (lpReplicaCollisionLeftCopyEmbedding G sites a b) ∪
        (Finset.univ : Finset
          (Copy (lpReplicaCurrentGraph G sites) b)).map
            (lpReplicaCollisionRightCopyEmbedding G sites a b) by
        rw [lpReplicaCollision_origin_union]
        exact Finset.mem_univ c)
    exact hU.resolve_left (Finset.mem_sdiff.mp hc).2

theorem lpReplicaCollision_currentCopies_left_false
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false false =
      Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  have hSL : S ⊆ L :=
    Finset.map_subset_map.mpr (Finset.subset_univ Sa)
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (false, false) ↔ c ∈ S
  change (if c ∈ L then
      (false, if c ∈ S then false else true)
    else
      (true, if c ∈ Sb.map
        (lpReplicaCollisionRightCopyEmbedding G sites a b) then false else true)) =
      (false, false) ↔ c ∈ S
  by_cases hcS : c ∈ S
  · simp [hcS, hSL hcS]
  · by_cases hcL : c ∈ L <;> simp [hcS, hcL]

theorem lpReplicaCollision_currentCopies_left_true
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false true =
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)) \ Sa).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
  rw [Finset.map_sdiff]
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (false, true) ↔
    c ∈ L \ S
  change (if c ∈ L then
      (false, if c ∈ S then false else true)
    else
      (true, if c ∈ Sb.map
        (lpReplicaCollisionRightCopyEmbedding G sites a b) then false else true)) =
      (false, true) ↔ c ∈ L \ S
  by_cases hcL : c ∈ L <;> by_cases hcS : c ∈ S <;>
    simp [hcL, hcS]

theorem lpReplicaCollision_currentCopies_right_false
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true false =
      Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let U := Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b)
  have hUL : Disjoint U L :=
    (lpReplicaCollision_origin_disjoint G sites a b).symm.mono
      (Finset.map_subset_map.mpr (Finset.subset_univ Sb)) Finset.Subset.rfl
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (true, false) ↔ c ∈ U
  change (if c ∈ L then (false, if c ∈ S then false else true)
    else (true, if c ∈ U then false else true)) = (true, false) ↔ c ∈ U
  by_cases hcU : c ∈ U
  · have hcL : c ∉ L := Finset.disjoint_left.mp hUL hcU
    simp [hcU, hcL]
  · by_cases hcL : c ∈ L <;> simp [hcU, hcL]

theorem lpReplicaCollision_currentCopies_right_true
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaCurrentCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true true =
      ((Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)) \ Sb).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
  rw [Finset.map_sdiff]
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let R := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) b)).map
      (lpReplicaCollisionRightCopyEmbedding G sites a b)
  let U := Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b)
  have hR : R = Finset.univ \ L :=
    lpReplicaCollision_rightOrigin_eq_sdiff G sites a b
  simp only [lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change lpReplicaCollisionRowTag G sites a b Sa Sb c = (true, true) ↔
    c ∈ R \ U
  change (if c ∈ L then (false, if c ∈ S then false else true)
    else (true, if c ∈ U then false else true)) = (true, true) ↔
      c ∈ R \ U
  rw [hR]
  by_cases hcL : c ∈ L <;> by_cases hcU : c ∈ U <;>
    simp [hcL, hcU]

theorem lpReplicaCollision_rowCopies_false
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false =
      (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ, true_and]
  change (lpReplicaCollisionRowTag G sites a b Sa Sb c).1 = false ↔ c ∈ L
  by_cases hcL : c ∈ L
  · have hcL' : c ∈ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]
  · have hcL' : c ∉ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]

theorem lpReplicaCollision_rowCopies_true
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true =
      (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) b)).map
          (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
  rw [lpReplicaCollision_rightOrigin_eq_sdiff]
  ext c
  let L := (Finset.univ : Finset
    (Copy (lpReplicaCurrentGraph G sites) a)).map
      (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  let S := Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b)
  simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  change (lpReplicaCollisionRowTag G sites a b Sa Sb c).1 = true ↔ c ∉ L
  by_cases hcL : c ∈ L
  · have hcL' : c ∈ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]
  · have hcL' : c ∉ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) := hcL
    simp [lpReplicaCollisionRowTag, hcL', hcL]

theorem lpReplicaCollision_leftSources
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (current : Bool) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCurrentCopies G sites
          (lpReplicaCollisionProfile G sites a b)
          (lpReplicaCollisionRowTag G sites a b Sa Sb) false current) =
      RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) a)
        (if current then Finset.univ \ Sa else Sa) := by
  cases current
  · rw [lpReplicaCollision_currentCopies_left_false]
    exact randomCurrent_sources_map_embedding _ _ _
      (lpReplicaCollisionLeftCopyEmbedding_ends G sites a b) Sa
  · rw [lpReplicaCollision_currentCopies_left_true]
    exact randomCurrent_sources_map_embedding _ _ _
      (lpReplicaCollisionLeftCopyEmbedding_ends G sites a b)
      (Finset.univ \ Sa)

theorem lpReplicaCollision_rightSources
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (current : Bool) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCurrentCopies G sites
          (lpReplicaCollisionProfile G sites a b)
          (lpReplicaCollisionRowTag G sites a b Sa Sb) true current) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) b)
        (if current then Finset.univ \ Sb else Sb)).map
          lpReplicaCurrentReflect.toEmbedding := by
  have hsource (T : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
      RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (lpReplicaCollisionProfile G sites a b))
          (T.map (lpReplicaCollisionRightCopyEmbedding G sites a b)) =
        (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) b) T).map
            lpReplicaCurrentReflect.toEmbedding := by
    calc
      RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (lpReplicaCollisionProfile G sites a b))
          (T.map (lpReplicaCollisionRightCopyEmbedding G sites a b)) =
        RandomCurrent.sources
          (fun c => Sym2.map lpReplicaCurrentReflect
            (endsM (lpReplicaCurrentGraph G sites) b c)) T :=
          randomCurrent_sources_map_embedding _ _ _
            (lpReplicaCollisionRightCopyEmbedding_ends G sites a b) T
      _ = RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (fun e => b (lpReplicaCurrentEdgeReflect G sites e)))
          (lpReplicaReflectCopies G sites b T) := by
          symm
          exact randomCurrent_sources_map_embedding _ _ _
            (lpReplicaReflectCopyEquiv_ends G sites b) T
      _ = (RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) b) T).map
            lpReplicaCurrentReflect.toEmbedding :=
          lpReplicaReflectCopies_sources G sites b T
  cases current
  · rw [lpReplicaCollision_currentCopies_right_false]
    exact hsource Sb
  · rw [lpReplicaCollision_currentCopies_right_true]
    exact hsource (Finset.univ \ Sb)

end CollisionTag

def lpReplicaToggleRows (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
  fun c => if c ∈ P then (!(tag c).1, (tag c).2) else tag c

theorem lpReplicaToggleRows_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Function.Involutive (lpReplicaToggleRows G sites m P) := by
  intro tag
  funext c
  by_cases hc : c ∈ P
  · cases htag : tag c with
    | mk row current =>
      cases row <;> cases current <;>
        simp [lpReplicaToggleRows, hc, htag]
  · simp [lpReplicaToggleRows, hc]

theorem lpReplicaRowCopies_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) row =
      lpReplicaRowCopies G sites m tag row ∆ P := by
  ext c
  by_cases hc : c ∈ P <;> cases hrow : (tag c).1 <;> cases row <;>
    simp [lpReplicaRowCopies, lpReplicaToggleRows, hc, hrow,
      Finset.mem_symmDiff]

theorem lpReplicaCurrentCopies_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites m
        (lpReplicaToggleRows G sites m P tag) row current =
      lpReplicaCurrentCopies G sites m tag row current ∆
        P.filter (fun c => (tag c).2 = current) := by
  ext c
  simp only [lpReplicaCurrentCopies, lpReplicaToggleRows, mem_filter,
    mem_univ, true_and, Finset.mem_symmDiff]
  by_cases hc : c ∈ P
  · simp only [hc, if_pos, true_and]
    rcases htag : tag c with ⟨r, q⟩
    cases r <;> cases q <;> cases row <;> cases current <;> simp
  · simp only [hc, if_neg, false_and, not_false_eq_true, and_true,
      or_false]

omit [DecidableEq V] in
theorem lpReplicaCurrentCopies_subset_rowCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites m tag row current ⊆
      lpReplicaRowCopies G sites m tag row := by
  intro c hc
  simp only [lpReplicaCurrentCopies, lpReplicaRowCopies, mem_filter,
    mem_univ, true_and] at hc ⊢
  exact congrArg Prod.fst hc

theorem lpReplicaRowCopies_eq_current_symmDiff
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites m tag row =
      lpReplicaCurrentCopies G sites m tag row false ∆
        lpReplicaCurrentCopies G sites m tag row true := by
  ext c
  cases htag : tag c with
  | mk r q =>
    cases r <;> cases q <;> cases row <;>
      simp [lpReplicaRowCopies, lpReplicaCurrentCopies, htag,
        Finset.mem_symmDiff]

theorem lpReplicaRowSources_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P tag) row) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaRowCopies G sites m tag row) ∆
        RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) P := by
  rw [lpReplicaRowCopies_toggle, RandomCurrent.sources_symmDiff]

theorem lpReplicaCurrentSources_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaCurrentCopies G sites m
          (lpReplicaToggleRows G sites m P tag) row current) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaCurrentCopies G sites m tag row current) ∆
        RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (P.filter (fun c => (tag c).2 = current)) := by
  rw [lpReplicaCurrentCopies_toggle, RandomCurrent.sources_symmDiff]

theorem lpReplicaRowSources_eq_currentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag row) =
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaCurrentCopies G sites m tag row false) ∆
        RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
          (lpReplicaCurrentCopies G sites m tag row true) := by
  rw [lpReplicaRowCopies_eq_current_symmDiff,
    RandomCurrent.sources_symmDiff]

def lpReplicaRowComponent (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    Finset (LPReplicaCurrentVertex V) :=
  RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaRowCopies G sites m tag row) root

theorem lpReplicaRowComponent_root_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    root ∈ lpReplicaRowComponent G sites m tag row root := by
  rw [lpReplicaRowComponent, RandomCurrent.mem_compOf]
  exact Relation.ReflTransGen.refl

theorem lpReplicaRowComponent_ghost1_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool)
    (hdisc : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m tag row)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
      lpReplicaRowComponent G sites m tag row lpReplicaCurrentGhost0 := by
  rw [lpReplicaRowComponent, RandomCurrent.mem_compOf]
  exact hdisc

section Reflection

variable [Fintype I] [DecidableEq I]

theorem lpReplicaRowComponent_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    lpReplicaRowComponent G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectTag G sites m tag) row
        (lpReplicaCurrentReflect root) =
      (lpReplicaRowComponent G sites m tag row root).map
        lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hy := lpReplicaCurrentReflect_involutive (V := V) y
  rw [← hy]
  simp only [lpReplicaRowComponent, RandomCurrent.mem_compOf]
  rw [lpReplicaRowConn_reflectTag]
  simp

end Reflection

def LPReplicaRowGate (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) : Prop :=
  let H := lpReplicaCurrentGraph G sites
  let e := endsM H m
  RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag false false) = A ∧
    RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag false true) = ∅ ∧
    ¬ RandomCurrent.connK e (lpReplicaRowCopies G sites m tag false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 ∧
    RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag true false) = B ∧
    RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag true true) = ∅ ∧
    ¬ RandomCurrent.connK e (lpReplicaRowCopies G sites m tag true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1

noncomputable instance lpReplicaRowGateDecidable
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    DecidablePred (LPReplicaRowGate G sites m A B) :=
  Classical.decPred _

section CollisionTag

variable [Fintype I] [DecidableEq I]

theorem lpReplicaCollisionRowGate
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (A B : Finset (LPReplicaCurrentVertex V))
    (hSa : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) a) Sa = A)
    (hSa' : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) a)
      (Finset.univ \ Sa) = ∅)
    (hda : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) a) Finset.univ
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hSb : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) b) Sb = B)
    (hSb' : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) b)
      (Finset.univ \ Sb) = ∅)
    (hdb : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) b) Finset.univ
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites a b) A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCollisionRowTag G sites a b Sa Sb) := by
  have hdisc0 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [lpReplicaCollision_rowCopies_false]
    exact fun h => hda
      ((randomCurrent_connK_map_embedding
        (endsM (lpReplicaCurrentGraph G sites) a)
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCollisionLeftCopyEmbedding G sites a b)
        (lpReplicaCollisionLeftCopyEmbedding_ends G sites a b)
        Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).1 h)
  have hdisc1 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [lpReplicaCollision_rowCopies_true]
    intro h
    let mappedEnds := fun c : Copy (lpReplicaCurrentGraph G sites) b =>
      Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) b c)
    have hmapped : RandomCurrent.connK mappedEnds Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 :=
      (randomCurrent_connK_map_embedding mappedEnds
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCollisionRightCopyEmbedding G sites a b)
        (lpReplicaCollisionRightCopyEmbedding_ends G sites a b)
        Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).1 h
    have hreflected : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => b (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites b Finset.univ)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 :=
      (randomCurrent_connK_map_embedding mappedEnds
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => b (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopyEquiv G sites b).toEmbedding
        (lpReplicaReflectCopyEquiv_ends G sites b)
        Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).2 hmapped
    have horiginal : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) b) Finset.univ
        lpReplicaCurrentGhost1 lpReplicaCurrentGhost0 := by
      have htransport :=
        (lpReplicaReflectCopies_connK G sites b Finset.univ
          lpReplicaCurrentGhost1 lpReplicaCurrentGhost0).1
      apply htransport
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hreflected
    exact hdb (RandomCurrent.connK_symm _ _ horiginal)
  unfold LPReplicaRowGate
  refine ⟨?_, ?_, hdisc0, ?_, ?_, hdisc1⟩
  · rw [lpReplicaCollision_leftSources]
    simpa using hSa
  · rw [lpReplicaCollision_leftSources]
    simpa using hSa'
  · rw [lpReplicaCollision_rightSources]
    simpa using congrArg
      (Finset.map lpReplicaCurrentReflect.toEmbedding) hSb
  · rw [lpReplicaCollision_rightSources]
    simpa using congrArg
      (Finset.map lpReplicaCurrentReflect.toEmbedding) hSb'

end CollisionTag

section Reflection

variable [Fintype I] [DecidableEq I]

theorem lpReplicaRowGate_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    LPReplicaRowGate G sites
      (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
      (A.map lpReplicaCurrentReflect.toEmbedding)
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaReflectTag G sites m tag) := by
  unfold LPReplicaRowGate at hgate ⊢
  have hdisc : ∀ row,
      (¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag row)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ->
      ¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaRowCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro row hrow hconn
    have hreflected : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaRowCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost1)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost0) := by
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hconn
    have horiginal :=
      (lpReplicaRowConn_reflectTag G sites m tag row
        lpReplicaCurrentGhost1 lpReplicaCurrentGhost0).1 hreflected
    exact hrow (RandomCurrent.connK_symm _ _ horiginal)
  refine ⟨?_, ?_, hdisc false hgate.2.2.1, ?_, ?_,
    hdisc true hgate.2.2.2.2.2⟩
  · rw [lpReplicaCurrentSources_reflectTag, hgate.1]
  · rw [lpReplicaCurrentSources_reflectTag, hgate.2.1]
    simp
  · rw [lpReplicaCurrentSources_reflectTag, hgate.2.2.2.1]
  · rw [lpReplicaCurrentSources_reflectTag, hgate.2.2.2.2.1]
    simp

end Reflection

theorem lpReplicaRowGate_rowSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag false) = A ∧
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag true) = B := by
  unfold LPReplicaRowGate at hgate
  constructor
  · rw [lpReplicaRowSources_eq_currentSources, hgate.1, hgate.2.1]
    simp
  · rw [lpReplicaRowSources_eq_currentSources, hgate.2.2.2.1,
      hgate.2.2.2.2.1]
    simp

theorem lpReplicaRowGate_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hgate : LPReplicaRowGate G sites m A B tag)
    (hsecond : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = true)) = ∅)
    (hdisc0 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let X := RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = false))
    LPReplicaRowGate G sites m (A ∆ X) (B ∆ X)
      (lpReplicaToggleRows G sites m P tag) := by
  dsimp only
  unfold LPReplicaRowGate at hgate ⊢
  refine ⟨?_, ?_, hdisc0, ?_, ?_, hdisc1⟩
  · rw [lpReplicaCurrentSources_toggle, hgate.1]
  · rw [lpReplicaCurrentSources_toggle, hgate.2.1, hsecond]
    simp
  · rw [lpReplicaCurrentSources_toggle, hgate.2.2.2.1]
  · rw [lpReplicaCurrentSources_toggle, hgate.2.2.2.2.1, hsecond]
    simp

theorem lpReplicaRowGate_toggle_offdiag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hgate : LPReplicaRowGate G sites m (Si ∆ Sj ∆ T) ∅ tag)
    (hfirst : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = false)) = Sj ∆ T)
    (hsecond : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = true)) = ∅)
    (hdisc0 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites m Si (Sj ∆ T)
      (lpReplicaToggleRows G sites m P tag) := by
  have h := lpReplicaRowGate_toggle G sites m (Si ∆ Sj ∆ T) ∅
    tag P hgate hsecond hdisc0 hdisc1
  dsimp only at h
  rw [hfirst] at h
  have hsource : (Si ∆ Sj ∆ T) ∆ (Sj ∆ T) = Si := by
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  rw [hsource] at h
  have hB : (∅ : Finset (LPReplicaCurrentVertex V)) ∆ (Sj ∆ T) =
      Sj ∆ T := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hB] at h
  exact h

end

end StatMech.Ising
