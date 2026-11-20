/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferFailedGate










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem exchangeFirstRow_no_incident_zero
    {ends : I -> Sym2 W} {K L : Finset I} {k zero : W}
    (hL : ¬ connK ends L k zero) :
    ∀ i ∈ exchangeFirstRow ends K L k zero, zero ∉ ends i := by
  classical
  intro i hi hzero
  rw [exchangeFirstRow, Finset.mem_union] at hi
  rcases hi with hi | hi
  · rcases Finset.mem_sdiff.mp hi with ⟨hiK, hin⟩
    exact hin (mem_edgeComponent_of_endpoint hiK hzero)
  · rw [edgeComponent, Finset.mem_filter] at hi
    exact hL (hi.2 zero hzero)


theorem exchangeSecondRow_no_incident_k
    {ends : I -> Sym2 W} {K L : Finset I} {k zero : W}
    (hK : ¬ connK ends K k zero) :
    ∀ i ∈ exchangeSecondRow ends K L k zero, k ∉ ends i := by
  classical
  intro i hi hk
  rw [exchangeSecondRow, Finset.mem_union] at hi
  rcases hi with hi | hi
  · rcases Finset.mem_sdiff.mp hi with ⟨hiL, hin⟩
    exact hin (mem_edgeComponent_of_endpoint hiL hk)
  · rw [edgeComponent, Finset.mem_filter] at hi
    exact hK (connK_symm ends K (hi.2 k hk))



theorem edgeComponent_eq_empty_of_no_incident
    (ends : I -> Sym2 W) (K : Finset I) (root : W)
    (hinc : ∀ i ∈ K, root ∉ ends i) :
    edgeComponent ends K root = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rw [edgeComponent, Finset.mem_filter] at hi
  let x := (ends i).out.1
  have hx : x ∈ ends i := Sym2.out_fst_mem (ends i)
  have hrx : root ≠ x := by
    intro h
    exact hinc i hi.1 (h ▸ hx)
  exact (not_connK_of_no_incident hrx hinc) (hi.2 x hx)




theorem canonicalTransferUnion_selfSwap_eq_empty
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalTransferUnion ends m k zero
      (balancedSwap m
        (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) = ∅ := by
  let d := balancedSwap m
    (canonicalMiddleTransfer ends m c k zero)
    (canonicalOuterTransfer ends m c k zero) c
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl hc
  have hfirst : edgeComponent ends (rowClass m d 0) zero = ∅ := by
    rw [hrows.1]
    apply edgeComponent_eq_empty_of_no_incident
    exact exchangeFirstRow_no_incident_zero hc.2.2.2.2.2
  have hsecond : edgeComponent ends (rowClass m d 1) k = ∅ := by
    rw [hrows.2]
    apply edgeComponent_eq_empty_of_no_incident
    exact exchangeSecondRow_no_incident_k hc.2.2.2.2.1
  rw [canonicalTransferUnion, canonicalTransfers_union, hfirst, hsecond]
  rfl



noncomputable def canonicalNormalRow
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) : Finset I :=
  rowClass m c 0 ∆ canonicalTransferUnion ends m k zero c




theorem canonicalTransferSymmDiff_eq_rowSymmDiff_of_normalRows
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c d : ↑m -> Fin 4)
    (hac : canonicalNormalRow ends m k zero a =
      canonicalNormalRow ends m k zero c)
    (hbd : canonicalNormalRow ends m k zero b =
      canonicalNormalRow ends m k zero d)
    (hrow : rowClass m c 0 ∆ rowClass m d 0 =
      canonicalTransferUnion ends m k zero a ∆
        canonicalTransferUnion ends m k zero b) :
    canonicalTransferUnion ends m k zero c ∆
        canonicalTransferUnion ends m k zero d =
      rowClass m a 0 ∆ rowClass m b 0 := by
  let Ra := rowClass m a 0
  let Rb := rowClass m b 0
  let Rc := rowClass m c 0
  let Rd := rowClass m d 0
  let Ta := canonicalTransferUnion ends m k zero a
  let Tb := canonicalTransferUnion ends m k zero b
  let Tc := canonicalTransferUnion ends m k zero c
  let Td := canonicalTransferUnion ends m k zero d
  change Ra ∆ Ta = Rc ∆ Tc at hac
  change Rb ∆ Tb = Rd ∆ Td at hbd
  change Rc ∆ Rd = Ta ∆ Tb at hrow
  change Tc ∆ Td = Ra ∆ Rb
  calc
    Tc ∆ Td = (Tc ∆ Td) ∆ (Rc ∆ Rc) ∆ (Rd ∆ Rd) := by simp
    _ = (Rc ∆ Tc) ∆ (Rd ∆ Td) ∆ Rc ∆ Rd := by ac_rfl
    _ = (Ra ∆ Ta) ∆ (Rb ∆ Tb) ∆ Rc ∆ Rd := by rw [← hac, ← hbd]
    _ = (Ra ∆ Rb) ∆ (Ta ∆ Tb) ∆ (Rc ∆ Rd) := by ac_rfl
    _ = (Ra ∆ Rb) ∆ (Rc ∆ Rd) ∆ (Rc ∆ Rd) := by rw [← hrow]
    _ = Ra ∆ Rb := by simp [symmDiff_assoc]

end StatMech.GrahamGHS.FourColor
