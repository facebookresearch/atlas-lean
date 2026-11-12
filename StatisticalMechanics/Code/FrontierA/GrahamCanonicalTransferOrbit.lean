/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex











open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]




def CanonicalMaskTransferAdjacent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) : Prop :=
  ∃ (q : rightMaskFiber ends m j k l zero p)
      (a b : leftMaskFiber ends m j k l zero p),
    q.1.1 = balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 ∧
      q.1.1 = balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1

theorem canonicalMaskTransferAdjacent_symm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Symmetric (CanonicalMaskTransferAdjacent ends m j k l zero p) := by
  intro c d h
  rcases h with ⟨q, a, b, hqc, hqd⟩
  exact ⟨q, b, a, hqd, hqc⟩



def CanonicalMaskTransferOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  Relation.ReflTransGen
    (CanonicalMaskTransferAdjacent ends m j k l zero p)

theorem canonicalMaskTransferOrbit_refl
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferOrbit ends m j k l zero p c c :=
  Relation.ReflTransGen.refl

theorem canonicalMaskTransferOrbit_symm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Symmetric (CanonicalMaskTransferOrbit ends m j k l zero p) :=
  Relation.ReflTransGen.symmetric
    (canonicalMaskTransferAdjacent_symm ends m j k l zero p)

theorem canonicalMaskTransferOrbit_trans
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Transitive (CanonicalMaskTransferOrbit ends m j k l zero p) := by
  intro a b c hab hbc
  exact hab.trans hbc



def IsCanonicalMaskOrbitSelector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p) : Prop :=
  (∀ c, CanonicalMaskTransferOrbit ends m j k l zero p c (rho c)) ∧
    ∀ c d, CanonicalMaskTransferOrbit ends m j k l zero p c d ->
      rho c = rho d



noncomputable def canonicalMaskOrbitScore
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    Nat ×ₗ Fin (Fintype.card (leftMaskFiber ends m j k l zero p)) :=
  toLex (canonicalTransferSize ends m k zero c.1.1,
    Fintype.equivFin (leftMaskFiber ends m j k l zero p) c)

theorem canonicalMaskOrbitScore_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Function.Injective (canonicalMaskOrbitScore ends m k zero p
      (j := j) (l := l)) := by
  intro c d h
  have hpair := congrArg ofLex h
  exact (Fintype.equivFin
    (leftMaskFiber ends m j k l zero p)).injective
      (congrArg Prod.snd hpair)


noncomputable def canonicalMaskTransferOrbitFinset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter
    (CanonicalMaskTransferOrbit ends m j k l zero p c)

@[simp] theorem mem_canonicalMaskTransferOrbitFinset_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c ↔
      CanonicalMaskTransferOrbit ends m j k l zero p c d := by
  classical
  simp [canonicalMaskTransferOrbitFinset]

theorem canonicalMaskTransferOrbitFinset_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskTransferOrbitFinset ends m j k l zero p c).Nonempty := by
  refine ⟨c, ?_⟩
  rw [mem_canonicalMaskTransferOrbitFinset_iff]
  exact canonicalMaskTransferOrbit_refl ends m j k l zero p c



noncomputable def canonicalMaskOrbitMinimumReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskTransferOrbitFinset ends m j k l zero p c).exists_min_image
      (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
      (canonicalMaskTransferOrbitFinset_nonempty
        ends m j k l zero p c))

theorem canonicalMaskOrbitMinimumReference_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitMinimumReference ends m j k l zero p c ∈
        canonicalMaskTransferOrbitFinset ends m j k l zero p c ∧
      ∀ d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c,
        canonicalMaskOrbitScore ends m k zero p
            (canonicalMaskOrbitMinimumReference ends m j k l zero p c) ≤
          canonicalMaskOrbitScore ends m k zero p d :=
  Classical.choose_spec
    ((canonicalMaskTransferOrbitFinset ends m j k l zero p c).exists_min_image
      (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
      (canonicalMaskTransferOrbitFinset_nonempty
        ends m j k l zero p c))

theorem canonicalMaskOrbitMinimumReference_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferOrbit ends m j k l zero p c
      (canonicalMaskOrbitMinimumReference ends m j k l zero p c) := by
  rw [← mem_canonicalMaskTransferOrbitFinset_iff]
  exact (canonicalMaskOrbitMinimumReference_spec
    ends m j k l zero p c).1

theorem canonicalMaskOrbitMinimumReference_score_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitScore ends m k zero p
        (canonicalMaskOrbitMinimumReference ends m j k l zero p c) ≤
      canonicalMaskOrbitScore ends m k zero p d := by
  apply (canonicalMaskOrbitMinimumReference_spec
    ends m j k l zero p c).2 d
  rwa [mem_canonicalMaskTransferOrbitFinset_iff]

theorem canonicalMaskOrbitMinimumReference_size_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalTransferSize ends m k zero
        (canonicalMaskOrbitMinimumReference ends m j k l zero p c).1.1 ≤
      canonicalTransferSize ends m k zero d.1.1 := by
  have hscore := canonicalMaskOrbitMinimumReference_score_le
    ends m j k l zero p c d hcd
  rw [canonicalMaskOrbitScore, canonicalMaskOrbitScore,
    Prod.Lex.toLex_le_toLex] at hscore
  omega

theorem canonicalMaskOrbitMinimumReference_eq_of_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitMinimumReference ends m j k l zero p c =
      canonicalMaskOrbitMinimumReference ends m j k l zero p d := by
  let rc := canonicalMaskOrbitMinimumReference ends m j k l zero p c
  let rd := canonicalMaskOrbitMinimumReference ends m j k l zero p d
  have hcrd : CanonicalMaskTransferOrbit ends m j k l zero p c rd :=
    hcd.trans (canonicalMaskOrbitMinimumReference_mem
      ends m j k l zero p d)
  have hdrc : CanonicalMaskTransferOrbit ends m j k l zero p d rc :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p hcd).trans
      (canonicalMaskOrbitMinimumReference_mem ends m j k l zero p c)
  have hle := canonicalMaskOrbitMinimumReference_score_le
    ends m j k l zero p c rd hcrd
  have hge := canonicalMaskOrbitMinimumReference_score_le
    ends m j k l zero p d rc hdrc
  apply canonicalMaskOrbitScore_injective ends m j k l zero p
  exact le_antisymm hle hge

theorem canonicalMaskOrbitMinimumReference_selector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    IsCanonicalMaskOrbitSelector ends m j k l zero p
      (canonicalMaskOrbitMinimumReference ends m j k l zero p) := by
  constructor
  · exact canonicalMaskOrbitMinimumReference_mem ends m j k l zero p
  · exact canonicalMaskOrbitMinimumReference_eq_of_orbit
      ends m j k l zero p



theorem canonicalTransfers_valid_on_sameMask
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    let X := canonicalMiddleTransfer ends m r.1.1 k zero
    let Y := canonicalOuterTransfer ends m r.1.1 k zero
    X ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 ∧
      Y ⊆ colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 ∧
      sources ends X = {k, l} ∧ sources ends Y = ∅ := by
  have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
  have hprofile :
      fourColorMaskProfile m r.1.1 = fourColorMaskProfile m c.1.1 :=
    r.2.trans c.2.symm
  have hmid : middleMask m r.1.1 = middleMask m c.1.1 :=
    congrArg Prod.fst hprofile
  have hout : outerMask m r.1.1 = outerMask m c.1.1 :=
    congrArg Prod.snd hprofile
  have hX : canonicalMiddleTransfer ends m r.1.1 k zero ⊆
      colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 := by
    have hr : canonicalMiddleTransfer ends m r.1.1 k zero ⊆
        middleMask m r.1.1 := by
      simpa only [middleMask] using hv.1
    rw [hmid] at hr
    simpa only [middleMask] using hr
  have hY : canonicalOuterTransfer ends m r.1.1 k zero ⊆
      colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 := by
    have hr : canonicalOuterTransfer ends m r.1.1 k zero ⊆
        outerMask m r.1.1 := by
      simpa only [outerMask] using hv.2.1
    rw [hout] at hr
    simpa only [outerMask] using hr
  exact ⟨hX, hY, hv.2.2.1, hv.2.2.2⟩



noncomputable def canonicalOrbitSelectorMaskFiberMap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p)
    (hdisconnect : ∀ c,
      RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
          (canonicalOuterTransfer ends m (rho c).1.1 k zero)
          c.1.1) k zero)
    (c : leftMaskFiber ends m j k l zero p) :
    rightMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransfer ends m (rho c).1.1 k zero
  let Y := canonicalOuterTransfer ends m (rho c).1.1 k zero
  let q := balancedSwap m X Y c.1.1
  have hv := canonicalTransfers_valid_on_sameMask
    hloop hjk hkl (rho c) c
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.1.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 (hdisconnect c)
  refine ⟨⟨q, hq⟩, ?_⟩
  calc
    fourColorMaskProfile m q = fourColorMaskProfile m c.1.1 :=
      fourColorMaskProfile_balancedSwap m X Y c.1.1
    _ = p := c.2



noncomputable def canonicalOrbitSelectorMaskFiberEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p)
    (hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho)
    (hdisconnect : ∀ c,
      RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
          (canonicalOuterTransfer ends m (rho c).1.1 k zero)
          c.1.1) k zero) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p where
  toFun := canonicalOrbitSelectorMaskFiberMap
    ends m j k l zero hloop hjk hkl p rho hdisconnect
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    have hval :
        balancedSwap m
            (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
            (canonicalOuterTransfer ends m (rho c).1.1 k zero) c.1.1 =
          balancedSwap m
            (canonicalMiddleTransfer ends m (rho d).1.1 k zero)
            (canonicalOuterTransfer ends m (rho d).1.1 k zero) d.1.1 := by
      have := congrArg
        (fun q : rightMaskFiber ends m j k l zero p => q.1.1) hcd
      simpa only [canonicalOrbitSelectorMaskFiberMap] using this
    have hadj : CanonicalMaskTransferAdjacent ends m j k l zero p c d := by
      refine ⟨canonicalOrbitSelectorMaskFiberMap
        ends m j k l zero hloop hjk hkl p rho hdisconnect c,
        rho c, rho d, rfl, ?_⟩
      simpa only [canonicalOrbitSelectorMaskFiberMap] using hval
    have hsame : rho c = rho d :=
      hrho.2 c d (Relation.ReflTransGen.single hadj)
    rw [← hsame] at hval
    have hinv := congrArg
      (balancedSwap m
        (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
        (canonicalOuterTransfer ends m (rho c).1.1 k zero)) hval
    simpa only [balancedSwap_involutive] using hinv


theorem leftMaskFiber_card_le_right_of_canonicalOrbitSelector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p)
    (hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho)
    (hdisconnect : ∀ c,
      RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
          (canonicalOuterTransfer ends m (rho c).1.1 k zero)
          c.1.1) k zero) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  Fintype.card_le_of_injective
    (canonicalOrbitSelectorMaskFiberEmbedding
      ends m j k l zero hloop hjk hkl p rho hrho hdisconnect)
    (canonicalOrbitSelectorMaskFiberEmbedding
      ends m j k l zero hloop hjk hkl p rho hrho hdisconnect).injective




def CanonicalMaskOrbitLocalDescent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c d : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p c d ->
    ¬ RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m c.1.1 k zero)
          (canonicalOuterTransfer ends m c.1.1 k zero)
          d.1.1) k zero ->
      canonicalTransferSize ends m k zero d.1.1 <
        canonicalTransferSize ends m k zero c.1.1



theorem canonicalMaskOrbitMinimumReference_disconnects
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hdescent : CanonicalMaskOrbitLocalDescent ends m j k l zero p)
    (d : leftMaskFiber ends m j k l zero p) :
    RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        (canonicalOuterTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        d.1.1) k zero := by
  by_contra hbad
  let r := canonicalMaskOrbitMinimumReference ends m j k l zero p d
  have hdr : CanonicalMaskTransferOrbit ends m j k l zero p d r :=
    canonicalMaskOrbitMinimumReference_mem ends m j k l zero p d
  have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
    canonicalMaskTransferOrbit_symm ends m j k l zero p hdr
  have hlt : canonicalTransferSize ends m k zero d.1.1 <
      canonicalTransferSize ends m k zero r.1.1 :=
    hdescent r d hrd (by simpa only [r] using hbad)
  have hle : canonicalTransferSize ends m k zero r.1.1 ≤
      canonicalTransferSize ends m k zero d.1.1 := by
    simpa only [r] using canonicalMaskOrbitMinimumReference_size_le
      ends m j k l zero p d d
        (canonicalMaskTransferOrbit_refl ends m j k l zero p d)
  exact (not_lt_of_ge hle) hlt


noncomputable def canonicalMaskOrbitDescentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hdescent : CanonicalMaskOrbitLocalDescent ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p :=
  canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p
    (canonicalMaskOrbitMinimumReference ends m j k l zero p)
    (canonicalMaskOrbitMinimumReference_selector ends m j k l zero p)
    (canonicalMaskOrbitMinimumReference_disconnects
      ends m j k l zero p hdescent)



theorem GrahamFiberMinor_of_canonicalMaskOrbitLocalDescent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hdescent : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitLocalDescent ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskwise
  intro p
  exact Fintype.card_le_of_injective
    (canonicalMaskOrbitDescentEmbedding
      ends m j k l zero hloop hjk hkl p (hdescent p))
    (canonicalMaskOrbitDescentEmbedding
      ends m j k l zero hloop hjk hkl p (hdescent p)).injective

end StatMech.GrahamGHS.FourColor
