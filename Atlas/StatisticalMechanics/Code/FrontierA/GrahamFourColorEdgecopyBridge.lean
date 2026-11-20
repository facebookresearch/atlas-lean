/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamFourColorProfileCount
import Code.FrontierA.GrahamWeightedFourReplicaCore

open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev GrahamFourSplit (total : G.edgeFinset -> Nat) :=
  {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) //
    forall e, pqr.1 e + pqr.2.1 e + pqr.2.2 e <= total e}


noncomputable def grahamFourSplitMultiplicityNat
    (total : G.edgeFinset -> Nat) (s : GrahamFourSplit G total) : Nat :=
  ∏ e : G.edgeFinset,
    (total e).choose (s.1.1 e) *
      (total e - s.1.1 e).choose (s.1.2.1 e) *
      (total e - s.1.1 e - s.1.2.1 e).choose (s.1.2.2 e)



noncomputable def grahamFourColorToSplit
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total)) : GrahamFourSplit G total :=
  if hq : q.IsPartition Finset.univ then
    ⟨(profileFlux G total q.color1,
      profileFlux G total q.color2,
      profileFlux G total q.color3),
      grahamFourColor_profile_sum_le G total q hq⟩
  else
    ⟨((fun _ => 0), (fun _ => 0), (fun _ => 0)), fun e => by simp⟩

theorem grahamFourColorToSplit_of_partition
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    (grahamFourColorToSplit G total q).1 =
      (profileFlux G total q.color1,
        profileFlux G total q.color2,
        profileFlux G total q.color3) := by
  simp [grahamFourColorToSplit, hq]



theorem grahamFourColor_edgecopy_bridge
    {M : Type*} [AddCommMonoid M]
    (total : G.edgeFinset -> Nat)
    (Theta : (G.edgeFinset -> Nat) -> (G.edgeFinset -> Nat) ->
      (G.edgeFinset -> Nat) -> M) :
    (∑ s : GrahamFourSplit G total,
      grahamFourSplitMultiplicityNat G total s •
        Theta s.1.1 s.1.2.1 s.1.2.2) =
      ∑ q ∈ grahamFourColorings
          (Finset.univ : Finset (Copy G total)),
        Theta (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3) := by
  let C := grahamFourColorings
    (Finset.univ : Finset (Copy G total))
  let g := grahamFourColorToSplit G total
  let F : GrahamFourSplit G total -> M := fun s =>
    Theta s.1.1 s.1.2.1 s.1.2.2
  have htheta : ∀ q, q ∈ C →
      Theta (profileFlux G total q.color1)
          (profileFlux G total q.color2)
          (profileFlux G total q.color3) = F (g q) := by
    intro q hq
    have hpart : q.IsPartition Finset.univ := by
      simpa [C] using hq
    simp only [F, g]
    rw [show (grahamFourColorToSplit G total q).1 =
        (profileFlux G total q.color1,
          profileFlux G total q.color2,
          profileFlux G total q.color3) from
      grahamFourColorToSplit_of_partition G total q hpart]
  rw [Finset.sum_congr rfl htheta, Finset.sum_comp F g]
  have himage : C.image g = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro s
    let fiber := C.filter (fun q =>
      profileFlux G total q.color1 = s.1.1 /\
        profileFlux G total q.color2 = s.1.2.1 /\
        profileFlux G total q.color3 = s.1.2.2)
    have hcard : #fiber = grahamFourSplitMultiplicityNat G total s := by
      simpa only [fiber, C, grahamFourSplitMultiplicityNat,
        mul_assoc] using
        grahamFourColor_edgecopy_profile_count G total
          s.1.1 s.1.2.1 s.1.2.2
    have hmult : 0 < grahamFourSplitMultiplicityNat G total s := by
      unfold grahamFourSplitMultiplicityNat
      apply Finset.prod_pos
      intro e he
      have hs := s.2 e
      apply Nat.mul_pos
      · apply Nat.mul_pos
        · exact Nat.choose_pos (by omega)
        · exact Nat.choose_pos (by omega)
      · exact Nat.choose_pos (by omega)
    have hfiber : fiber.Nonempty :=
      Finset.card_pos.mp (hcard.symm ▸ hmult)
    obtain ⟨q, hq⟩ := hfiber
    have hqC : q ∈ C := (Finset.mem_filter.mp hq).1
    have hqprof := (Finset.mem_filter.mp hq).2
    rw [Finset.mem_image]
    refine ⟨q, hqC, ?_⟩
    apply Subtype.ext
    have hpart : q.IsPartition Finset.univ := by
      simpa [C] using hqC
    rw [grahamFourColorToSplit_of_partition G total q hpart]
    exact Prod.ext hqprof.1 (Prod.ext hqprof.2.1 hqprof.2.2)
  rw [himage]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  have hfiber : #(C.filter fun q => g q = s) =
      grahamFourSplitMultiplicityNat G total s := by
    rw [show C.filter (fun q => g q = s) = C.filter (fun q =>
        profileFlux G total q.color1 = s.1.1 /\
          profileFlux G total q.color2 = s.1.2.1 /\
          profileFlux G total q.color3 = s.1.2.2) by
      apply Finset.filter_congr
      intro q hqC
      have hpart : q.IsPartition Finset.univ := by
        simpa [C] using hqC
      rw [show g q = s <-> (g q).1 = s.1 by
        exact Subtype.ext_iff]
      rw [show (g q).1 =
          (profileFlux G total q.color1,
            profileFlux G total q.color2,
            profileFlux G total q.color3) by
        exact grahamFourColorToSplit_of_partition G total q hpart]
      constructor
      · intro h
        exact ⟨congrArg Prod.fst h,
          congrArg (fun p => p.2.1) h,
          congrArg (fun p => p.2.2) h⟩
      · rintro ⟨h1, h2, h3⟩
        exact Prod.ext h1 (Prod.ext h2 h3)]
    simpa only [C, grahamFourSplitMultiplicityNat, mul_assoc] using
      grahamFourColor_edgecopy_profile_count G total
        s.1.1 s.1.2.1 s.1.2.2
  exact hfiber.symm

end StatMech.FrontierA
