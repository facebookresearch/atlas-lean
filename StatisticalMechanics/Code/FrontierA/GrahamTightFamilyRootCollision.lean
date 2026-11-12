/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalEdgeDegreeHall











open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



abbrev CanonicalTightOpposingRootCuts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 d.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero a.1.1 d.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero b.1.1 c.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero a.1.1 d.1.1



abbrev CanonicalTightTwoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  ∃ q1 q2 : rightMaskFiber ends m j k l zero p,
      q1 ≠ q2 ∧
      q1 ∈ canonicalMaskRightImages ends m j k l zero p c ∧
      q1 ∈ canonicalMaskRightImages ends m j k l zero p d ∧
      q2 ∈ canonicalMaskRightImages ends m j k l zero p c ∧
      q2 ∈ canonicalMaskRightImages ends m j k l zero p d



abbrev CanonicalTightRootCollisionDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  CanonicalTightOpposingRootCuts ends m j k l zero p c d ∨
    CanonicalTightTwoRowCollision ends m j k l zero p c d

omit [Fintype I] in



theorem canonicalMaskRightAugmentedMatching_rotateSquare
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d e : ↑S) (hdc : d ≠ c) (hec : e ≠ c) (hed : e ≠ d)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (q r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hfd : f d = some q) (hfe : f e = some r)
    (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1)
    (hrd : r.1 ∈ canonicalMaskRightImages ends m j k l zero p d.1) :
    ∃ g : canonicalMaskRightAugmentedEquivType
        ends m j k l zero p S,
      CanonicalMaskRightAugmentedMatching
        ends m j k l zero p S e g := by
  classical
  let π : Equiv.Perm ↑S := (Equiv.swap c d).trans (Equiv.swap e c)
  let g : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S := π.trans f
  have hπe : π e = c := by
    rw [show π e = (Equiv.swap e c) ((Equiv.swap c d) e) by rfl,
      Equiv.swap_apply_of_ne_of_ne hec hed, Equiv.swap_apply_left]
  have hπc : π c = d := by
    rw [show π c = (Equiv.swap e c) ((Equiv.swap c d) c) by rfl,
      Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hed.symm hdc]
  have hπd : π d = e := by
    rw [show π d = (Equiv.swap e c) ((Equiv.swap c d) d) by rfl,
      Equiv.swap_apply_right, Equiv.swap_apply_right]
  refine ⟨g, ?_, ?_⟩
  · change f (π e) = none
    rw [hπe]
    exact hf.1
  · intro x hxe
    by_cases hxc : x = c
    · subst x
      refine ⟨q, ?_, hqc⟩
      change f (π c) = some q
      rw [hπc]
      exact hfd
    by_cases hxd : x = d
    · subst x
      refine ⟨r, ?_, hrd⟩
      change f (π d) = some r
      rw [hπd]
      exact hfe
    obtain ⟨s, hfs, hsx⟩ := hf.2 x hxc
    refine ⟨s, ?_, hsx⟩
    change f (π x) = some s
    have hπx : π x = x := by
      rw [show π x = (Equiv.swap e c) ((Equiv.swap c d) x) by rfl,
        Equiv.swap_apply_of_ne_of_ne hxc hxd,
        Equiv.swap_apply_of_ne_of_ne hxe hxc]
    rw [hπx]
    exact hfs

omit [Fintype I] in


theorem canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S) (hdc : d ≠ c)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (q r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hfd : f d = some q) (hqr : q ≠ r)
    (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1)
    (hrd : r.1 ∈ canonicalMaskRightImages ends m j k l zero p d.1) :
    ∃ e : ↑S, e ≠ c ∧ e ≠ d ∧ f e = some r ∧
      ∃ g : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S,
        CanonicalMaskRightAugmentedMatching
          ends m j k l zero p S e g := by
  classical
  let e : ↑S := f.symm (some r)
  have hfe : f e = some r := by simp [e]
  have hec : e ≠ c := by
    intro h
    have hnone : f e = none := (congrArg f h).trans hf.1
    rw [hnone] at hfe
    cases hfe
  have hed : e ≠ d := by
    intro h
    have hrq : r = q := Option.some.inj
      (hfe.symm.trans ((congrArg f h).trans hfd))
    exact hqr hrq.symm
  exact ⟨e, hec, hed, hfe,
    canonicalMaskRightAugmentedMatching_rotateSquare
      ends m j k l zero p S c d e hdc hec hed f hf q r hfd hfe hqc hrd⟩

set_option maxHeartbeats 1000000 in




theorem canonicalMaskRightAugmentedRootCollision_cut_or_reroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (q : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1) :
    (∃ d : ↑S, d ≠ c ∧
      CanonicalTightOpposingRootCuts
        ends m j k l zero p c.1 d.1) ∨
      ∃ e : ↑S, e ≠ c ∧
        ∃ g : canonicalMaskRightAugmentedEquivType
            ends m j k l zero p S,
          CanonicalMaskRightAugmentedMatching
            ends m j k l zero p S e g := by
  classical
  let d : ↑S := f.symm (some q)
  have hfd : f d = some q := by simp [d]
  have hdc : d ≠ c := by
    intro h
    have hnone : f d = none := (congrArg f h).trans hf.1
    rw [hnone] at hfd
    cases hfd
  obtain ⟨s, hfs, hsd⟩ := hf.2 d hdc
  have hsq : s = q := Option.some.inj (hfs.symm.trans hfd)
  have hqd : q.1 ∈ canonicalMaskRightImages
      ends m j k l zero p d.1 := by
    simpa only [hsq] using hsd
  have hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c.1 d.1 :=
    (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c.1 d.1).mp ⟨q.1, hqc, hqd⟩
  have hcdne : c.1 ≠ d.1 := by
    intro h
    exact hdc (Subtype.ext h.symm)
  rcases canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages
      hloop hjk hkl c.1 d.1 hcdne hcd with hcuts | hsquare
  · exact Or.inl ⟨d, hdc, hcuts⟩
  · obtain ⟨q1, q2, hq12, hq1c, hq1d, hq2c, hq2d⟩ := hsquare
    by_cases hq1 : q1 = q.1
    · have hq2S : q2 ∈ canonicalMaskRightNeighborhood
          ends m j k l zero p S :=
        (mem_canonicalMaskRightNeighborhood_iff
          ends m j k l zero p S q2).mpr ⟨c.1, c.2, hq2c⟩
      let r : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S) := ⟨q2, hq2S⟩
      have hqr : q ≠ r := by
        intro h
        exact hq12 (hq1.trans (congrArg Subtype.val h))
      obtain ⟨e, hec, -, -, g, hg⟩ :=
        canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
          ends m j k l zero p S c d hdc f hf q r hfd hqr hqc hq2d
      exact Or.inr ⟨e, hec, g, hg⟩
    · have hq1S : q1 ∈ canonicalMaskRightNeighborhood
          ends m j k l zero p S :=
        (mem_canonicalMaskRightNeighborhood_iff
          ends m j k l zero p S q1).mpr ⟨c.1, c.2, hq1c⟩
      let r : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S) := ⟨q1, hq1S⟩
      have hqr : q ≠ r := by
        intro h
        exact hq1 (congrArg Subtype.val h).symm
      obtain ⟨e, hec, -, -, g, hg⟩ :=
        canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
          ends m j k l zero p S c d hdc f hf q r hfd hqr hqc hq1d
      exact Or.inr ⟨e, hec, g, hg⟩




theorem tightFamily_rootCollisionDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c) :
    ∃ d ∈ S, d ≠ c ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p d ∧
      CanonicalTightRootCollisionDichotomy
        ends m j k l zero p c d := by
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hc herase q hqc
  have hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d :=
    (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩
  exact ⟨d, hdS, hdc, hqd,
    canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages
      hloop hjk hkl c d hdc.symm hcd⟩




theorem exists_tightFamily_allRootCollisionDichotomies_of_not_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
      (canonicalMaskRightNeighborhood
          ends m j k l zero p S).card + 1 = S.card ∧
      ∀ c ∈ S, ∀ q,
        q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        ∃ d ∈ S, d ≠ c ∧
          q ∈ canonicalMaskRightImages ends m j k l zero p d ∧
          CanonicalTightRootCollisionDichotomy
            ends m j k l zero p c d := by
  obtain ⟨S, hSne, htight, herase, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  refine ⟨S, hSne, htight, ?_⟩
  intro c hc q hqc
  exact tightFamily_rootCollisionDichotomy
    ends m j k l zero hloop hjk hkl p S c hc (herase c hc) q hqc

set_option maxHeartbeats 1000000 in




theorem exists_tightFamily_allRootCollisionReroutes_of_not_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
      (canonicalMaskRightNeighborhood
          ends m j k l zero p S).card + 1 = S.card ∧
      ∀ c : ↑S,
        ∃ f : canonicalMaskRightAugmentedEquivType
            ends m j k l zero p S,
          CanonicalMaskRightAugmentedMatching
              ends m j k l zero p S c f ∧
            ∀ q : ↑(canonicalMaskRightNeighborhood
                ends m j k l zero p S),
              q.1 ∈ canonicalMaskRightImages
                  ends m j k l zero p c.1 ->
                ((∃ d : ↑S, d ≠ c ∧
                    CanonicalTightOpposingRootCuts
                      ends m j k l zero p c.1 d.1) ∨
                  ∃ e : ↑S, e ≠ c ∧
                    ∃ g : canonicalMaskRightAugmentedEquivType
                        ends m j k l zero p S,
                      CanonicalMaskRightAugmentedMatching
                        ends m j k l zero p S e g) := by
  classical
  obtain ⟨S, hSne, htight, -, hproper, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  refine ⟨S, hSne, htight, ?_⟩
  intro c
  obtain ⟨f, hfc, hf⟩ := exists_canonicalMaskRightAugmentedEquiv
    ends m j k l zero p S htight hproper c.1 c.2
  have hmatch : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f := by
    refine ⟨hfc, ?_⟩
    intro x hxc
    exact hf x (fun h => hxc (Subtype.ext h))
  refine ⟨f, hmatch, ?_⟩
  intro q hqc
  exact canonicalMaskRightAugmentedRootCollision_cut_or_reroute
    ends m j k l zero hloop hjk hkl p S c f hmatch q hqc

end StatMech.GrahamGHS.FourColor
