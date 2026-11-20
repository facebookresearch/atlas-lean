/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.Z2GaugeTypedFKCylinder

open scoped BigOperators

namespace StatMech.FrontierA

noncomputable section


def finiteGeom (r : Real) (N : Nat) : Real :=
  ∑ d ∈ Finset.range N, r ^ d



theorem sum_fin_pow_natDist_le_two_finiteGeom
    {N : Nat} (r : Real) (hr : 0 <= r) (i : Fin N) :
    (∑ j : Fin N, r ^ Nat.dist i.val j.val) <= 2 * finiteGeom r N := by
  let code : Fin N -> Fin N × Bool := fun j =>
    (⟨Nat.dist i.val j.val, by
      have hi := i.isLt
      have hj := j.isLt
      simp only [Nat.dist]
      omega⟩, decide (i.val <= j.val))
  have hcode : Function.Injective code := by
    intro j₁ j₂ h
    have hdist : Nat.dist i.val j₁.val = Nat.dist i.val j₂.val := by
      exact congrArg (fun q : Fin N × Bool => q.1.val) h
    have hside : (i.val <= j₁.val) ↔ (i.val <= j₂.val) := by
      have hb := congrArg (fun q : Fin N × Bool => q.2) h
      simpa [code] using hb
    apply Fin.ext
    by_cases h₁ : i.val <= j₁.val
    · have h₂ : i.val <= j₂.val := hside.mp h₁
      rw [Nat.dist_eq_sub_of_le h₁, Nat.dist_eq_sub_of_le h₂] at hdist
      omega
    · have h₂ : ¬ i.val <= j₂.val := fun hle => h₁ (hside.mpr hle)
      have hj₁ : j₁.val <= i.val := Nat.le_of_lt (Nat.lt_of_not_ge h₁)
      have hj₂ : j₂.val <= i.val := Nat.le_of_lt (Nat.lt_of_not_ge h₂)
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hj₁,
        Nat.dist_comm, Nat.dist_eq_sub_of_le hj₂] at hdist
      omega
  calc
    (∑ j : Fin N, r ^ Nat.dist i.val j.val) =
        ∑ q ∈ (Finset.univ : Finset (Fin N)).image code, r ^ q.1.val := by
      rw [Finset.sum_image hcode.injOn]
    _ <= ∑ q : Fin N × Bool, r ^ q.1.val := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun _ _ => Finset.mem_univ _
      · intro q _ _
        positivity
    _ = 2 * finiteGeom r N := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, Finset.sum_add_distrib]
      rw [two_mul]
      congr 1 <;>
        exact Fin.sum_univ_eq_sum_range (fun d => r ^ d) N



theorem finiteGeom_le_inv_one_sub
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) (N : Nat) :
    finiteGeom r N <= (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  rw [finiteGeom, geom_sum_eq hne]
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hrpow : 0 <= r ^ N := pow_nonneg hr0 N
  rw [div_eq_mul_inv]
  have hrewrite : (r ^ N - 1) * (r - 1)⁻¹ =
      (1 - r ^ N) * (1 - r)⁻¹ := by
    rw [show r - 1 = -(1 - r) by ring, inv_neg]
    ring
  rw [hrewrite]
  exact mul_le_of_le_one_left (inv_nonneg.mpr hden.le) (by linarith)



theorem sum_fin_prod_pow_l1_le_four_finiteGeom_sq
    {N : Nat} (r : Real) (hr : 0 <= r) (x y : Fin N) (depth : Nat) :
    (∑ ij : Fin N × Fin N,
        r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)) <=
      4 * (finiteGeom r N) ^ 2 * r ^ depth := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hx := sum_fin_pow_natDist_le_two_finiteGeom r hr x
  have hy := sum_fin_pow_natDist_le_two_finiteGeom r hr y
  have hpow : 0 <= r ^ depth := pow_nonneg hr _
  calc
    (∑ ij : Fin N × Fin N,
        r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)) =
        ((∑ i : Fin N, r ^ Nat.dist x.val i.val) *
          (∑ j : Fin N, r ^ Nat.dist y.val j.val)) * r ^ depth := by
      rw [Fintype.sum_prod_type]
      simp_rw [pow_add]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      congr 1
      exact (Finset.sum_mul Finset.univ
        (fun i : Fin N => r ^ Nat.dist x.val i.val)
        (∑ j : Fin N, r ^ Nat.dist y.val j.val)).symm
    _ <= ((2 * finiteGeom r N) * (2 * finiteGeom r N)) * r ^ depth := by
      gcongr
    _ = 4 * (finiteGeom r N) ^ 2 * r ^ depth := by ring



theorem sum_union_le_add_of_nonneg
    {alpha : Type*} [DecidableEq alpha] (s t : Finset alpha)
    (f : alpha -> Real) (hf : forall x, 0 <= f x) :
    ∑ x ∈ s ∪ t, f x <= (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have hinter : 0 <= ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x _ => hf x
  linarith [Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)]



theorem nat_mul_pow_le_finiteGeom
    {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1) (N : Nat) :
    (N : Real) * r ^ N <= finiteGeom r N := by
  calc
    (N : Real) * r ^ N = ∑ _d ∈ Finset.range N, r ^ N := by simp
    _ <= ∑ d ∈ Finset.range N, r ^ d := by
      apply Finset.sum_le_sum
      intro d hd
      exact pow_le_pow_of_le_one hr0 hr1 (Finset.mem_range.mp hd).le
    _ = finiteGeom r N := rfl



theorem sum_fin_pow_reverseDepth_le_finiteGeom
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1) :
    (∑ z : Fin N, r ^ (N - z.val)) <= finiteGeom r N := by
  let revPerm : Equiv.Perm (Fin N) :=
    Function.Involutive.toPerm Fin.rev (fun z => Fin.rev_rev z)
  calc
    (∑ z : Fin N, r ^ (N - z.val)) <=
        ∑ z : Fin N, r ^ (Fin.rev z).val := by
      apply Finset.sum_le_sum
      intro z _
      apply pow_le_pow_of_le_one hr0 hr1
      simp only [Fin.rev]
      omega
    _ = ∑ z : Fin N, r ^ z.val := by
      simpa [revPerm] using
        (Equiv.sum_comp revPerm (fun z : Fin N => r ^ z.val))
    _ = finiteGeom r N := by
      exact Fin.sum_univ_eq_sum_range (fun d => r ^ d) N



def squareLayerExpSum {N : Nat} (r : Real) (x y : Fin N)
    (depth : Nat) : Real :=
  ∑ ij : Fin N × Fin N,
    r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)


def squareLowerCapExpSum (r : Real) (N : Nat) : Real :=
  ∑ xy : Fin N × Fin N, squareLayerExpSum r xy.1 xy.2 N


def squareXSideExpSum {N : Nat} (r : Real) (xBoundary : Fin N) : Real :=
  ∑ yz : Fin N × Fin N,
    squareLayerExpSum r xBoundary yz.1 (N - yz.2.val)


def squareYSideExpSum {N : Nat} (r : Real) (yBoundary : Fin N) : Real :=
  ∑ xz : Fin N × Fin N,
    squareLayerExpSum r xz.1 yBoundary (N - xz.2.val)

theorem squareLowerCapExpSum_le
    {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1) (N : Nat) :
    squareLowerCapExpSum r N <=
      4 * finiteGeom r N ^ 3 * N := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  calc
    squareLowerCapExpSum r N <=
        (N : Real) ^ 2 * (4 * finiteGeom r N ^ 2 * r ^ N) := by
      unfold squareLowerCapExpSum
      calc
        (∑ xy : Fin N × Fin N, squareLayerExpSum r xy.1 xy.2 N) <=
            ∑ _xy : Fin N × Fin N,
              4 * finiteGeom r N ^ 2 * r ^ N := by
          apply Finset.sum_le_sum
          intro xy _
          exact sum_fin_prod_pow_l1_le_four_finiteGeom_sq
            r hr0 xy.1 xy.2 N
        _ = (N : Real) ^ 2 *
              (4 * finiteGeom r N ^ 2 * r ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            nsmul_eq_mul, Nat.cast_mul]
          simp only [Fintype.card_fin]
          ring
    _ <= 4 * finiteGeom r N ^ 3 * N := by
      have hNr := nat_mul_pow_le_finiteGeom hr0 hr1 N
      calc
        (N : Real) ^ 2 * (4 * finiteGeom r N ^ 2 * r ^ N) =
            (4 * finiteGeom r N ^ 2 * N) * (N * r ^ N) := by ring
        _ <= (4 * finiteGeom r N ^ 2 * N) * finiteGeom r N := by
          gcongr
        _ = 4 * finiteGeom r N ^ 3 * N := by ring

theorem squareXSideExpSum_le
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1)
    (xBoundary : Fin N) :
    squareXSideExpSum r xBoundary <=
      4 * finiteGeom r N ^ 3 * N := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hdepth := sum_fin_pow_reverseDepth_le_finiteGeom
    (N := N) hr0 hr1
  unfold squareXSideExpSum
  rw [Fintype.sum_prod_type]
  calc
    (∑ y : Fin N, ∑ z : Fin N,
        squareLayerExpSum r xBoundary y (N - z.val)) <=
      ∑ y : Fin N, ∑ z : Fin N,
        4 * finiteGeom r N ^ 2 * r ^ (N - z.val) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      exact sum_fin_prod_pow_l1_le_four_finiteGeom_sq
        r hr0 xBoundary y (N - z.val)
    _ = (N : Real) *
        (4 * finiteGeom r N ^ 2 *
          (∑ z : Fin N, r ^ (N - z.val))) := by
      simp_rw [← Finset.mul_sum]
      simp [Fintype.card_fin]
      ring
    _ <= 4 * finiteGeom r N ^ 3 * N := by
      calc
        (N : Real) * (4 * finiteGeom r N ^ 2 *
            (∑ z : Fin N, r ^ (N - z.val))) <=
            N * (4 * finiteGeom r N ^ 2 * finiteGeom r N) := by
          gcongr
        _ = 4 * finiteGeom r N ^ 3 * N := by ring

theorem squareYSideExpSum_le
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1)
    (yBoundary : Fin N) :
    squareYSideExpSum r yBoundary <=
      4 * finiteGeom r N ^ 3 * N := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hdepth := sum_fin_pow_reverseDepth_le_finiteGeom
    (N := N) hr0 hr1
  unfold squareYSideExpSum
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin N, ∑ z : Fin N,
        squareLayerExpSum r x yBoundary (N - z.val)) <=
      ∑ x : Fin N, ∑ z : Fin N,
        4 * finiteGeom r N ^ 2 * r ^ (N - z.val) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      exact sum_fin_prod_pow_l1_le_four_finiteGeom_sq
        r hr0 x yBoundary (N - z.val)
    _ = (N : Real) *
        (4 * finiteGeom r N ^ 2 *
          (∑ z : Fin N, r ^ (N - z.val))) := by
      simp_rw [← Finset.mul_sum]
      simp [Fintype.card_fin]
      ring
    _ <= 4 * finiteGeom r N ^ 3 * N := by
      calc
        (N : Real) * (4 * finiteGeom r N ^ 2 *
            (∑ z : Fin N, r ^ (N - z.val))) <=
            N * (4 * finiteGeom r N ^ 2 * finiteGeom r N) := by
          gcongr
        _ = 4 * finiteGeom r N ^ 3 * N := by ring



theorem squareCylinderCoordinateExpSum_le
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1)
    (west east south north : Fin N) :
    squareLowerCapExpSum r N +
        squareXSideExpSum r west + squareXSideExpSum r east +
        squareYSideExpSum r south + squareYSideExpSum r north <=
      20 * finiteGeom r N ^ 3 * N := by
  have hcap := squareLowerCapExpSum_le hr0 hr1 N
  have hwest := squareXSideExpSum_le hr0 hr1 west
  have heast := squareXSideExpSum_le hr0 hr1 east
  have hsouth := squareYSideExpSum_le hr0 hr1 south
  have hnorth := squareYSideExpSum_le hr0 hr1 north
  linarith


theorem squareCylinderCoordinateExpSum_le_inv
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r < 1)
    (west east south north : Fin N) :
    squareLowerCapExpSum r N +
        squareXSideExpSum r west + squareXSideExpSum r east +
        squareYSideExpSum r south + squareYSideExpSum r north <=
      20 * ((1 - r)⁻¹) ^ 3 * N := by
  have hgeom := finiteGeom_le_inv_one_sub hr0 hr1 N
  have hgeom0 : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hinv0 : 0 <= (1 - r)⁻¹ := by
    positivity
  calc
    _ <= 20 * finiteGeom r N ^ 3 * N :=
      squareCylinderCoordinateExpSum_le hr0 hr1.le
        west east south north
    _ <= 20 * ((1 - r)⁻¹) ^ 3 * N := by
      gcongr




abbrev centralSquareSide (n : Nat) := n + 1


def centralSquareSheetHeight (n : Nat) :
    Fin (centralSquareSide n + centralSquareSide n + 1) :=
  ⟨centralSquareSide n, by omega⟩

private def centralLowerZ {n : Nat} (z : Fin (centralSquareSide n)) :
    Fin (centralSquareSide n + centralSquareSide n) :=
  Fin.castLE (by omega) z

@[simp] theorem centralLowerZ_val {n : Nat}
    (z : Fin (centralSquareSide n)) :
    (centralLowerZ z).val = z.val := rfl

private def centralBottomZ (n : Nat) :
    Fin (centralSquareSide n + centralSquareSide n) :=
  ⟨0, by simp [centralSquareSide]⟩

@[simp] theorem centralBottomZ_val (n : Nat) :
    (centralBottomZ n).val = 0 := rfl

@[simp] theorem finForward_eq_none_iff' {m : Nat} (f : Fin (m + 1)) :
    finForward f = none ↔ f = Fin.last m := by
  refine Fin.lastCases ?_ (fun z => ?_) f
  · simp [finForward]
  · simp [finForward]

def centralLowerBottomVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xy => some (CubicalCell.mk xy.1 xy.2 (centralBottomZ n)))

def centralLowerWestVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun yz => some (CubicalCell.mk 0 yz.1 (centralLowerZ yz.2)))

def centralLowerEastVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun yz => some
      (CubicalCell.mk (Fin.last n) yz.1 (centralLowerZ yz.2)))

def centralLowerSouthVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xz => some (CubicalCell.mk xz.1 0 (centralLowerZ xz.2)))

def centralLowerNorthVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xz => some
      (CubicalCell.mk xz.1 (Fin.last n) (centralLowerZ xz.2)))


def centralLowerBoundaryVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  centralLowerBottomVertices n ∪ centralLowerWestVertices n ∪
    centralLowerEastVertices n ∪ centralLowerSouthVertices n ∪
      centralLowerNorthVertices n

theorem cubicalLowerComplementInnerVertices_central_subset
    (n : Nat) :
    cubicalLowerComplementInnerVertices
        (a := centralSquareSide n) (b := centralSquareSide n)
        (c := centralSquareSide n + centralSquareSide n)
        (centralSquareSheetHeight n) ⊆
      centralLowerBoundaryVertices n := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hcut : p ∈ multibondCut
      (cubicalDualEnds
        (a := centralSquareSide n) (b := centralSquareSide n)
        (c := centralSquareSide n + centralSquareSide n))
      (cubicalBelowSpin (centralSquareSheetHeight n)) :=
    (Finset.mem_sdiff.mp hp).1
  have hnot : p ∉ cubicalXYSheet (centralSquareSheetHeight n) :=
    (Finset.mem_sdiff.mp hp).2
  have htrue := typedTrueEndpoint_spin_eq_true_of_mem_cut
    (cubicalDualEnds
      (a := centralSquareSide n) (b := centralSquareSide n)
      (c := centralSquareSide n + centralSquareSide n))
    (cubicalBelowSpin (centralSquareSheetHeight n)) p hcut
  rw [mem_multibondCut] at hcut
  cases p with
  | xy i j f =>
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          have hforward : finForward
              (0 : Fin (centralSquareSide n + centralSquareSide n + 1)) =
              some (centralBottomZ n) := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hend : typedTrueEndpoint
              (cubicalDualEnds
                (a := centralSquareSide n) (b := centralSquareSide n)
                (c := centralSquareSide n + centralSquareSide n))
              (cubicalBelowSpin (centralSquareSheetHeight n))
              (CubicalPlaquette.xy i j 0) =
              some (CubicalCell.mk i j (centralBottomZ n)) := by
            simp [typedTrueEndpoint, cubicalDualEnds, hforward,
              hb, cubicalBelowSpin, centralBottomZ]
          rw [hend]
          simp [centralLowerBoundaryVertices, centralLowerBottomVertices]
      | some z =>
          cases hf : finForward f with
          | none =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut
              have hlast : f =
                  Fin.last (centralSquareSide n + centralSquareSide n) :=
                (finForward_eq_none_iff' f).mp hf
              have hsucc : f = z.succ :=
                (finBackward_eq_some_iff f z).mp hb
              have hzval : z.val + 1 =
                  centralSquareSide n + centralSquareSide n := by
                have := congrArg Fin.val (hsucc.symm.trans hlast)
                simpa using this
              simp [centralSquareSide] at hzval hcut
              omega
          | some w =>
              have hsucc : f = z.succ :=
                (finBackward_eq_some_iff f z).mp hb
              have hcast : f = w.castSucc :=
                (finForward_eq_some_iff f w).mp hf
              have hzw : w.val = z.val + 1 := by
                have := congrArg Fin.val (hsucc.symm.trans hcast)
                simpa using this.symm
              have hfval : f.val = z.val + 1 := by rw [hsucc]; simp
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut
              have hcenter : f = centralSquareSheetHeight n := by
                apply Fin.ext
                simp [centralSquareSheetHeight, centralSquareSide] at hfval ⊢
                omega
              apply False.elim
              apply hnot
              rw [hcenter]
              simp [cubicalXYSheet]
  | xz i f z =>
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let y0 : Fin (centralSquareSide n) := 0
          have hforward : finForward
              (0 : Fin (centralSquareSide n + 1)) = some y0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < centralSquareSide n := by
            simp [cubicalDualEnds, hforward, cubicalBelowSpin,
              hb, centralSquareSheetHeight, centralSquareSide] at hcut
            simpa [centralSquareSide] using hcut
          let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
          have hzcast : centralLowerZ zlow = z := by
            apply Fin.ext
            rfl
          have hend : typedTrueEndpoint cubicalDualEnds
              (cubicalBelowSpin (centralSquareSheetHeight n))
              (CubicalPlaquette.xz i
                (0 : Fin (centralSquareSide n + 1)) z) =
              some (CubicalCell.mk i
                (0 : Fin (centralSquareSide n)) z) := by
            simp [typedTrueEndpoint, cubicalDualEnds, hforward,
              hb, cubicalBelowSpin, y0]
          rw [hend]
          unfold centralLowerBoundaryVertices
          apply Finset.mem_union_left (centralLowerNorthVertices n)
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(i, zlow), Finset.mem_univ _, by simp [hzcast]⟩
      | some y =>
          cases hf : finForward f with
          | none =>
              have hyLast : y = Fin.last n := by
                have hflast : f = Fin.last (centralSquareSide n) :=
                  (finForward_eq_none_iff' f).mp hf
                have hsucc : f = y.succ :=
                  (finBackward_eq_some_iff f y).mp hb
                apply Fin.ext
                have := congrArg Fin.val (hsucc.symm.trans hflast)
                simp [centralSquareSide] at this ⊢
                omega
              subst y
              have hz : z.val < centralSquareSide n := by
                simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  centralSquareSheetHeight, centralSquareSide] at hcut
                simpa [centralSquareSide] using hcut
              let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
              have hzcast : centralLowerZ zlow = z := by
                apply Fin.ext
                rfl
              have hend : typedTrueEndpoint cubicalDualEnds
                  (cubicalBelowSpin (centralSquareSheetHeight n))
                  (CubicalPlaquette.xz i f z) =
                  some (CubicalCell.mk i (Fin.last n) z) := by
                simp [typedTrueEndpoint, cubicalDualEnds, hb, hf,
                  cubicalBelowSpin, centralSquareSheetHeight,
                  centralSquareSide, hz]
              rw [hend]
              unfold centralLowerBoundaryVertices
              apply Finset.mem_union_right
              exact Finset.mem_image.mpr
                ⟨(i, zlow), Finset.mem_univ _, by simp [hzcast]⟩
          | some y' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut
  | yz f j z =>
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let x0 : Fin (centralSquareSide n) := 0
          have hforward : finForward
              (0 : Fin (centralSquareSide n + 1)) = some x0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < centralSquareSide n := by
            simp [cubicalDualEnds, hforward, cubicalBelowSpin,
              hb, centralSquareSheetHeight, centralSquareSide] at hcut
            simpa [centralSquareSide] using hcut
          let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
          have hzcast : centralLowerZ zlow = z := by
            apply Fin.ext
            rfl
          have hend : typedTrueEndpoint cubicalDualEnds
              (cubicalBelowSpin (centralSquareSheetHeight n))
              (CubicalPlaquette.yz
                (0 : Fin (centralSquareSide n + 1)) j z) =
              some (CubicalCell.mk
                (0 : Fin (centralSquareSide n)) j z) := by
            simp [typedTrueEndpoint, cubicalDualEnds, hforward,
              hb, cubicalBelowSpin, x0]
          rw [hend]
          unfold centralLowerBoundaryVertices
          apply Finset.mem_union_left (centralLowerNorthVertices n)
          apply Finset.mem_union_left (centralLowerSouthVertices n)
          apply Finset.mem_union_left (centralLowerEastVertices n)
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(j, zlow), Finset.mem_univ _, by simp [hzcast]⟩
      | some x =>
          cases hf : finForward f with
          | none =>
              have hxLast : x = Fin.last n := by
                have hflast : f = Fin.last (centralSquareSide n) :=
                  (finForward_eq_none_iff' f).mp hf
                have hsucc : f = x.succ :=
                  (finBackward_eq_some_iff f x).mp hb
                apply Fin.ext
                have := congrArg Fin.val (hsucc.symm.trans hflast)
                simp [centralSquareSide] at this ⊢
                omega
              subst x
              have hz : z.val < centralSquareSide n := by
                simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  centralSquareSheetHeight, centralSquareSide] at hcut
                simpa [centralSquareSide] using hcut
              let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
              have hzcast : centralLowerZ zlow = z := by
                apply Fin.ext
                rfl
              have hend : typedTrueEndpoint cubicalDualEnds
                  (cubicalBelowSpin (centralSquareSheetHeight n))
                  (CubicalPlaquette.yz f j z) =
                  some (CubicalCell.mk (Fin.last n) j z) := by
                simp [typedTrueEndpoint, cubicalDualEnds, hb, hf,
                  cubicalBelowSpin, centralSquareSheetHeight,
                  centralSquareSide, hz]
              rw [hend]
              unfold centralLowerBoundaryVertices
              apply Finset.mem_union_left (centralLowerNorthVertices n)
              apply Finset.mem_union_left (centralLowerSouthVertices n)
              apply Finset.mem_union_right
              exact Finset.mem_image.mpr
                ⟨(j, zlow), Finset.mem_univ _, by simp [hzcast]⟩
          | some x' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut


private def centralUpperZ (n : Nat) :
    Fin (centralSquareSide n + centralSquareSide n) :=
  ⟨centralSquareSide n, by simp [centralSquareSide]⟩

@[simp] theorem centralUpperZ_val (n : Nat) :
    (centralUpperZ n).val = centralSquareSide n := rfl

def centralUpperLayerVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xy => some (CubicalCell.mk xy.1 xy.2 (centralUpperZ n)))

theorem cubicalXYSheetUpperVertices_central_eq (n : Nat) :
    cubicalXYSheetUpperVertices
        (a := centralSquareSide n) (b := centralSquareSide n)
        (c := centralSquareSide n + centralSquareSide n)
        (centralSquareSheetHeight n) =
      centralUpperLayerVertices n := by
  rw [cubicalXYSheetUpperVertices_eq_layer]
  · unfold centralUpperLayerVertices
    apply Finset.image_congr
    intro xy _
    congr 2
  · simp [centralSquareSheetHeight, centralSquareSide]
  · simp [centralSquareSheetHeight, centralSquareSide]



def cubicalDualL1 {a b c : Nat} :
    CubicalDualVertex a b c -> CubicalDualVertex a b c -> Nat
  | some q, some q' =>
      Nat.dist q.x.val q'.x.val + Nat.dist q.y.val q'.y.val +
        Nat.dist q.z.val q'.z.val
  | _, _ => 0

private theorem centralBottomEmbedding_injective (n : Nat) :
    Function.Injective (fun xy :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xy.1 xy.2 (centralBottomZ n))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

private theorem centralUpperEmbedding_injective (n : Nat) :
    Function.Injective (fun xy :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xy.1 xy.2 (centralUpperZ n))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

theorem centralLowerBottom_doubleSum_eq
    (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerBottomVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareLowerCapExpSum r (centralSquareSide n) := by
  change (∑ uv ∈ centralLowerBottomVertices n ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) = _
  rw [Finset.sum_product (centralLowerBottomVertices n)
    (centralUpperLayerVertices n)]
  unfold centralLowerBottomVertices centralUpperLayerVertices
  rw [Finset.sum_image (centralBottomEmbedding_injective n).injOn]
  simp_rw [Finset.sum_image (centralUpperEmbedding_injective n).injOn]
  unfold squareLowerCapExpSum squareLayerExpSum cubicalDualL1
  apply Finset.sum_congr rfl
  intro xy _
  apply Finset.sum_congr rfl
  intro ij _
  congr 2
  simp [centralBottomZ, centralUpperZ, Nat.dist]

private theorem centralXSideEmbedding_injective (n : Nat)
    (xBoundary : Fin (centralSquareSide n)) :
    Function.Injective (fun yz :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xBoundary yz.1 (centralLowerZ yz.2))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  have hz : x.2.val = y.2.val := congrArg
    (fun q : Fin (centralSquareSide n + centralSquareSide n) => q.val) h.2.2
  apply Prod.ext h.2.1
  exact Fin.ext hz

private theorem centralYSideEmbedding_injective (n : Nat)
    (yBoundary : Fin (centralSquareSide n)) :
    Function.Injective (fun xz :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xz.1 yBoundary (centralLowerZ xz.2))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  have hz : x.2.val = y.2.val := congrArg
    (fun q : Fin (centralSquareSide n + centralSquareSide n) => q.val) h.2.2
  apply Prod.ext h.1
  exact Fin.ext hz

private theorem centralXSide_doubleSum_eq
    (r : Real) (n : Nat) (xBoundary : Fin (centralSquareSide n)) :
    (∑ uv ∈ ((Finset.univ : Finset
          (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
          (fun yz => some
            (CubicalCell.mk xBoundary yz.1 (centralLowerZ yz.2)))).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareXSideExpSum r xBoundary := by
  change (∑ uv ∈ ((Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
        (fun yz => some
          (CubicalCell.mk xBoundary yz.1 (centralLowerZ yz.2)))) ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) = _
  rw [Finset.sum_product]
  unfold centralUpperLayerVertices
  rw [Finset.sum_image
    (centralXSideEmbedding_injective n xBoundary).injOn]
  simp_rw [Finset.sum_image (centralUpperEmbedding_injective n).injOn]
  unfold squareXSideExpSum squareLayerExpSum cubicalDualL1
  apply Finset.sum_congr rfl
  intro yz _
  apply Finset.sum_congr rfl
  intro ij _
  congr 2
  simp [centralLowerZ, centralUpperZ, Nat.dist]

private theorem centralYSide_doubleSum_eq
    (r : Real) (n : Nat) (yBoundary : Fin (centralSquareSide n)) :
    (∑ uv ∈ ((Finset.univ : Finset
          (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
          (fun xz => some
            (CubicalCell.mk xz.1 yBoundary (centralLowerZ xz.2)))).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareYSideExpSum r yBoundary := by
  change (∑ uv ∈ ((Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
        (fun xz => some
          (CubicalCell.mk xz.1 yBoundary (centralLowerZ xz.2)))) ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) = _
  rw [Finset.sum_product]
  unfold centralUpperLayerVertices
  rw [Finset.sum_image
    (centralYSideEmbedding_injective n yBoundary).injOn]
  simp_rw [Finset.sum_image (centralUpperEmbedding_injective n).injOn]
  unfold squareYSideExpSum squareLayerExpSum cubicalDualL1
  apply Finset.sum_congr rfl
  intro xz _
  apply Finset.sum_congr rfl
  intro ij _
  congr 2
  simp [centralLowerZ, centralUpperZ, Nat.dist]

theorem centralLowerWest_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerWestVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareXSideExpSum r (0 : Fin (centralSquareSide n)) := by
  simpa [centralLowerWestVertices] using
    centralXSide_doubleSum_eq r n (0 : Fin (centralSquareSide n))

theorem centralLowerEast_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerEastVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareXSideExpSum r (Fin.last n) := by
  simpa [centralLowerEastVertices] using
    centralXSide_doubleSum_eq r n (Fin.last n)

theorem centralLowerSouth_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerSouthVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareYSideExpSum r (0 : Fin (centralSquareSide n)) := by
  simpa [centralLowerSouthVertices] using
    centralYSide_doubleSum_eq r n (0 : Fin (centralSquareSide n))

theorem centralLowerNorth_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerNorthVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareYSideExpSum r (Fin.last n) := by
  simpa [centralLowerNorthVertices] using
    centralYSide_doubleSum_eq r n (Fin.last n)

theorem centralLowerBoundary_doubleSum_le_coordinate
    {r : Real} (hr : 0 <= r) (n : Nat) :
    (∑ uv ∈ (centralLowerBoundaryVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) <=
      squareLowerCapExpSum r (centralSquareSide n) +
        squareXSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareXSideExpSum r (Fin.last n) +
        squareYSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareYSideExpSum r (Fin.last n) := by
  let f : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Real := fun u =>
    ∑ v ∈ centralUpperLayerVertices n, r ^ cubicalDualL1 u v
  have hf : forall u, 0 <= f u := by
    intro u
    unfold f
    positivity
  let A := centralLowerBottomVertices n
  let W := centralLowerWestVertices n
  let E := centralLowerEastVertices n
  let S := centralLowerSouthVertices n
  let T := centralLowerNorthVertices n
  have hAW := sum_union_le_add_of_nonneg A W f hf
  have hAWE := sum_union_le_add_of_nonneg (A ∪ W) E f hf
  have hAWES := sum_union_le_add_of_nonneg ((A ∪ W) ∪ E) S f hf
  have hAWEST := sum_union_le_add_of_nonneg (((A ∪ W) ∪ E) ∪ S) T f hf
  have hpieces :
      (∑ u ∈ ((((A ∪ W) ∪ E) ∪ S) ∪ T), f u) <=
        (∑ u ∈ A, f u) + (∑ u ∈ W, f u) +
          (∑ u ∈ E, f u) + (∑ u ∈ S, f u) +
            ∑ u ∈ T, f u := by
    linarith
  change (∑ uv ∈ centralLowerBoundaryVertices n ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) <= _
  rw [Finset.sum_product]
  change (∑ u ∈ centralLowerBoundaryVertices n, f u) <= _
  have hbottom : (∑ u ∈ A, f u) =
      squareLowerCapExpSum r (centralSquareSide n) := by
    simpa [A, f, Finset.sum_product] using
      centralLowerBottom_doubleSum_eq r n
  have hwest : (∑ u ∈ W, f u) =
      squareXSideExpSum r (0 : Fin (centralSquareSide n)) := by
    simpa [W, f, Finset.sum_product] using
      centralLowerWest_doubleSum_eq r n
  have heast : (∑ u ∈ E, f u) =
      squareXSideExpSum r (Fin.last n) := by
    simpa [E, f, Finset.sum_product] using
      centralLowerEast_doubleSum_eq r n
  have hsouth : (∑ u ∈ S, f u) =
      squareYSideExpSum r (0 : Fin (centralSquareSide n)) := by
    simpa [S, f, Finset.sum_product] using
      centralLowerSouth_doubleSum_eq r n
  have hnorth : (∑ u ∈ T, f u) =
      squareYSideExpSum r (Fin.last n) := by
    simpa [T, f, Finset.sum_product] using
      centralLowerNorth_doubleSum_eq r n
  rw [centralLowerBoundaryVertices]
  exact hpieces.trans_eq (by rw [hbottom, hwest, heast, hsouth, hnorth])



theorem cubicalLowerSlab_central_pow_l1_sum_le
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) (n : Nat) :
    (∑ uv ∈
        (cubicalLowerComplementInnerVertices
          (a := centralSquareSide n) (b := centralSquareSide n)
          (c := centralSquareSide n + centralSquareSide n)
          (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)),
      r ^ cubicalDualL1 uv.1 uv.2) <=
      20 * ((1 - r)⁻¹) ^ 3 * centralSquareSide n := by
  rw [cubicalXYSheetUpperVertices_central_eq]
  have hsub :
      (cubicalLowerComplementInnerVertices
          (a := centralSquareSide n) (b := centralSquareSide n)
          (c := centralSquareSide n + centralSquareSide n)
          (centralSquareSheetHeight n)).product
        (centralUpperLayerVertices n) ⊆
      (centralLowerBoundaryVertices n).product
        (centralUpperLayerVertices n) := by
    intro uv huv
    have hmem := Finset.mem_product.mp huv
    exact Finset.mem_product.mpr
      ⟨cubicalLowerComplementInnerVertices_central_subset n hmem.1,
        hmem.2⟩
  calc
    _ <= ∑ uv ∈ (centralLowerBoundaryVertices n).product
          (centralUpperLayerVertices n),
        r ^ cubicalDualL1 uv.1 uv.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro uv _ _
      positivity
    _ <= squareLowerCapExpSum r (centralSquareSide n) +
        squareXSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareXSideExpSum r (Fin.last n) +
        squareYSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareYSideExpSum r (Fin.last n) :=
      centralLowerBoundary_doubleSum_le_coordinate hr0 n
    _ <= 20 * ((1 - r)⁻¹) ^ 3 * centralSquareSide n :=
      squareCylinderCoordinateExpSum_le_inv hr0 hr1
        (0 : Fin (centralSquareSide n)) (Fin.last n)
        (0 : Fin (centralSquareSide n)) (Fin.last n)

theorem exp_neg_mul_natCast_eq_pow_exp_neg
    (decay : Real) (d : Nat) :
    Real.exp (-decay * (d : Real)) = Real.exp (-decay) ^ d := by
  rw [show -decay * (d : Real) = (d : Real) * (-decay) by ring,
    Real.exp_nat_mul]

theorem cubicalLowerSlab_central_exp_l1_sum_le
    (decay : Real) (hdecay : 0 < decay) (n : Nat) :
    (∑ uv ∈
        (cubicalLowerComplementInnerVertices
          (a := centralSquareSide n) (b := centralSquareSide n)
          (c := centralSquareSide n + centralSquareSide n)
          (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)),
      Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) <=
      20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n := by
  simpa only [exp_neg_mul_natCast_eq_pow_exp_neg] using
    (cubicalLowerSlab_central_pow_l1_sum_le
      (r := Real.exp (-decay)) (Real.exp_pos _).le
      (by rw [Real.exp_lt_one_iff]; linarith) n)

theorem none_not_mem_centralLowerBoundaryVertices (n : Nat) :
    (none : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) ∉
      centralLowerBoundaryVertices n := by
  simp [centralLowerBoundaryVertices, centralLowerBottomVertices,
    centralLowerWestVertices, centralLowerEastVertices,
    centralLowerSouthVertices, centralLowerNorthVertices]

theorem none_not_mem_centralUpperLayerVertices (n : Nat) :
    (none : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) ∉
      centralUpperLayerVertices n := by
  simp [centralUpperLayerVertices]

theorem cubicalLowerSlab_central_l1_pos
    (n : Nat)
    (uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) ×
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈
      (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n))) :
    0 < cubicalDualL1 uv.1 uv.2 := by
  have hmem := Finset.mem_product.mp huv
  have hsource := cubicalLowerComplementInnerVertices_central_subset n hmem.1
  have htarget : uv.2 ∈ centralUpperLayerVertices n := by
    rw [← cubicalXYSheetUpperVertices_central_eq]
    exact hmem.2
  have hne := cubicalLowerSlab_pair_ne
    (centralSquareSheetHeight n)
    (by simp [centralSquareSheetHeight, centralSquareSide]) uv huv
  cases hu : uv.1 with
  | none =>
      exact (none_not_mem_centralLowerBoundaryVertices n (hu ▸ hsource)).elim
  | some q =>
      cases hv : uv.2 with
      | none =>
          exact (none_not_mem_centralUpperLayerVertices n (hv ▸ htarget)).elim
      | some q' =>
          by_contra hnonpos
          have hzero : cubicalDualL1 (some q) (some q') = 0 := by omega
          simp only [cubicalDualL1] at hzero
          have hx : Nat.dist q.x.val q'.x.val = 0 := by omega
          have hy : Nat.dist q.y.val q'.y.val = 0 := by omega
          have hz : Nat.dist q.z.val q'.z.val = 0 := by omega
          apply hne
          rw [hu, hv]
          simp only [Option.some.injEq]
          have hxFin : q.x = q'.x :=
            Fin.ext (Nat.eq_of_dist_eq_zero hx)
          have hyFin : q.y = q'.y :=
            Fin.ext (Nat.eq_of_dist_eq_zero hy)
          have hzFin : q.z = q'.z :=
            Fin.ext (Nat.eq_of_dist_eq_zero hz)
          rcases q with ⟨qx, qy, qz⟩
          rcases q' with ⟨qx', qy', qz'⟩
          simp only at hxFin hyFin hzFin
          rw [hxFin, hyFin, hzFin]

theorem cubicalLowerSlab_central_l1_ge_one
    (n : Nat)
    (uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) ×
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈
      (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n))) :
    (1 : Real) <= cubicalDualL1 uv.1 uv.2 := by
  exact_mod_cast cubicalLowerSlab_central_l1_pos n uv huv



theorem cubicalXYWilson_central_perimeterLower_of_l1_decay
    (n : Nat)
    (K : CubicalPlaquette (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Real)
    (hK : forall p, 0 < K p)
    (decay : Real) (hdecay : 0 < decay)
    (hcorr : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
          (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)) ->
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
        Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) :
    Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
            (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
          centralSquareSide n) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (cubicalXYLoop (centralSquareSheetHeight n)) := by
  apply cubicalXYWilson_perimeterLower_of_lowerSlab_exponential
    (by simp [centralSquareSide]) (by simp [centralSquareSide])
    (by simp [centralSquareSide])
    (centralSquareSheetHeight n)
    (by simp [centralSquareSheetHeight, centralSquareSide])
    K hK decay (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)
    (centralSquareSide n) hdecay
    (fun uv => (cubicalDualL1 uv.1 uv.2 : Real))
  · exact cubicalLowerSlab_central_l1_ge_one n
  · exact hcorr
  · exact cubicalLowerSlab_central_exp_l1_sum_le decay hdecay n


end

end StatMech.FrontierA
