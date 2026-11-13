/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.TorusPeriodicLift





namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_edgeBit {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) : Fin 2 :=
  if e ∈ F then 1 else 0

def ons_horizontalBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : Fin 2 :=
  ons_edgeBit F (ons_portEdge L (p, 0))

def ons_verticalBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : Fin 2 :=
  ons_edgeBit F (ons_portEdge L (p, 1))

@[simp] theorem ons_edgeBit_eq_one_iff
    {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) :
    ons_edgeBit F e = 1 ↔ e ∈ F := by
  simp [ons_edgeBit]

@[simp] theorem ons_edgeBit_eq_zero_iff
    {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) :
    ons_edgeBit F e = 0 ↔ e ∉ F := by
  simp [ons_edgeBit]

theorem ons_portEdge_west_eq_horizontal
    (L : ℕ) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 2) =
      ons_portEdge L ((p.1 - 1, p.2), 0) := by
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep, Sym2.eq_iff]

theorem ons_portEdge_south_eq_vertical
    (L : ℕ) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 3) =
      ons_portEdge L ((p.1, p.2 - 1), 1) := by
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep, Sym2.eq_iff]



theorem ons_edgeBits_divergence_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_horizontalBit F p + ons_horizontalBit F (p.1 - 1, p.2) +
      ons_verticalBit F p + ons_verticalBit F (p.1, p.2 - 1) = 0 := by
  have hsum := ons_evenSubgraph_neighbor_sum_zero
    (onsTorusGraph L) F hF p
  rw [ons_torus_neighbor_sum_eq_direction_sum] at hsum
  rw [Fin.sum_univ_four] at hsum
  change
    ons_edgeBit F (ons_portEdge L (p, 0)) +
      ons_edgeBit F (ons_portEdge L (p, 1)) +
      ons_edgeBit F (ons_portEdge L (p, 2)) +
      ons_edgeBit F (ons_portEdge L (p, 3)) = 0 at hsum
  rw [ons_portEdge_west_eq_horizontal,
    ons_portEdge_south_eq_vertical] at hsum
  change
    ons_horizontalBit F p + ons_verticalBit F p +
      ons_horizontalBit F (p.1 - 1, p.2) +
      ons_verticalBit F (p.1, p.2 - 1) = 0 at hsum
  simpa [add_assoc, add_left_comm, add_comm] using hsum


noncomputable def ons_edgeCycleIntersection
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) : Fin 2 :=
  ∑ p : ZMod L × ZMod L,
    (ons_horizontalBit F p *
        ons_verticalBit G (p.1, p.2 - 1) +
      ons_verticalBit F p *
        ons_horizontalBit G (p.1 - 1, p.2))

theorem ons_edgeBit_eq_zero_of_incCount_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (v : V) (e : Sym2 V)
    (hinc : incCount F v = 0) (hve : v ∈ e) :
    ons_edgeBit F e = 0 := by
  by_cases heF : e ∈ F
  · have hpos : 0 < incCount F v := by
      unfold incCount
      apply Finset.card_pos.mpr
      exact ⟨e, Finset.mem_filter.mpr ⟨heF, hve⟩⟩
    rw [hinc] at hpos
    omega
  · simp [ons_edgeBit, heF]

theorem ons_horizontalBit_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_horizontalBit F p = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L (p, 0)) hinc
  simp [ons_portEdge]

theorem ons_verticalBit_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_verticalBit F p = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L (p, 1)) hinc
  simp [ons_portEdge]

theorem ons_verticalBit_pred_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_verticalBit F (p.1, p.2 - 1) = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L ((p.1, p.2 - 1), 1)) hinc
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep]

theorem ons_horizontalBit_pred_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_horizontalBit F (p.1 - 1, p.2) = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L ((p.1 - 1, p.2), 0)) hinc
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep]

theorem ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hdisj : ∀ p, incCount F p = 0 ∨ incCount G p = 0) :
    ons_edgeCycleIntersection F G = 0 := by
  unfold ons_edgeCycleIntersection
  apply Finset.sum_eq_zero
  intro p _
  rcases hdisj p with hF | hG
  · rw [ons_horizontalBit_zero_of_incCount_eq_zero F p hF,
      ons_verticalBit_zero_of_incCount_eq_zero F p hF]
    simp
  · rw [ons_verticalBit_pred_zero_of_incCount_eq_zero G p hG,
      ons_horizontalBit_pred_zero_of_incCount_eq_zero G p hG]
    simp

def ons_horizontalZBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  (ons_horizontalBit F p : ZMod 2)

def ons_verticalZBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  (ons_verticalBit F p : ZMod 2)

noncomputable def ons_xFlux {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (x : ZMod L) : ZMod 2 :=
  ∑ y : ZMod L, ons_horizontalZBit F (x, y)

noncomputable def ons_yFlux {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (y : ZMod L) : ZMod 2 :=
  ∑ x : ZMod L, ons_verticalZBit F (x, y)

theorem ons_edgeZBits_divergence_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_horizontalZBit F p +
      ons_horizontalZBit F (p.1 - 1, p.2) +
      ons_verticalZBit F p +
      ons_verticalZBit F (p.1, p.2 - 1) = 0 := by
  exact_mod_cast ons_edgeBits_divergence_zero L F hF p

theorem ons_xFlux_pred
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (x : ZMod L) :
    ons_xFlux F x = ons_xFlux F (x - 1) := by
  have hsum :
      ∑ y : ZMod L,
        (ons_horizontalZBit F (x, y) +
          ons_horizontalZBit F (x - 1, y) +
          ons_verticalZBit F (x, y) +
          ons_verticalZBit F (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    exact ons_edgeZBits_divergence_zero L F hF (x, y)
  simp only [Finset.sum_add_distrib] at hsum
  have hvshift :
      (∑ y : ZMod L, ons_verticalZBit F (x, y - 1)) =
        ∑ y : ZMod L, ons_verticalZBit F (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y => ons_verticalZBit F (x, y)))
  rw [hvshift] at hsum
  change ons_xFlux F x = ons_xFlux F (x - 1)
  unfold ons_xFlux
  have hzero :
      (∑ y : ZMod L, ons_horizontalZBit F (x, y)) +
        (∑ y : ZMod L, ons_horizontalZBit F (x - 1, y)) = 0 := by
    let A := ∑ y : ZMod L, ons_horizontalZBit F (x, y)
    let B := ∑ y : ZMod L, ons_horizontalZBit F (x - 1, y)
    let C := ∑ y : ZMod L, ons_verticalZBit F (x, y)
    change A + B + C + C = 0 at hsum
    change A + B = 0
    calc
      A + B = (A + B) + (C + C) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
      _ = A + B + C + C := by abel
      _ = 0 := hsum
  exact (eq_neg_of_add_eq_zero_left hzero).trans
    (CharTwo.neg_eq _)

theorem ons_yFlux_pred
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (y : ZMod L) :
    ons_yFlux F y = ons_yFlux F (y - 1) := by
  have hsum :
      ∑ x : ZMod L,
        (ons_horizontalZBit F (x, y) +
          ons_horizontalZBit F (x - 1, y) +
          ons_verticalZBit F (x, y) +
          ons_verticalZBit F (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact ons_edgeZBits_divergence_zero L F hF (x, y)
  simp only [Finset.sum_add_distrib] at hsum
  have hhshift :
      (∑ x : ZMod L, ons_horizontalZBit F (x - 1, y)) =
        ∑ x : ZMod L, ons_horizontalZBit F (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x => ons_horizontalZBit F (x, y)))
  rw [hhshift] at hsum
  change ons_yFlux F y = ons_yFlux F (y - 1)
  unfold ons_yFlux
  have hzero :
      (∑ x : ZMod L, ons_verticalZBit F (x, y)) +
        (∑ x : ZMod L, ons_verticalZBit F (x, y - 1)) = 0 := by
    let A := ∑ x : ZMod L, ons_horizontalZBit F (x, y)
    let C := ∑ x : ZMod L, ons_verticalZBit F (x, y)
    let D := ∑ x : ZMod L, ons_verticalZBit F (x, y - 1)
    change A + A + C + D = 0 at hsum
    change C + D = 0
    calc
      C + D = (A + A) + (C + D) := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = A + A + C + D := by abel
      _ = 0 := hsum
  exact (eq_neg_of_add_eq_zero_left hzero).trans
    (CharTwo.neg_eq _)

def ons_xSeamPortEdge (L : ℕ) (y : ZMod L) :
    Sym2 (ZMod L × ZMod L) :=
  ons_portEdge L (((-1 : ZMod L), y), 0)

def ons_ySeamPortEdge (L : ℕ) (x : ZMod L) :
    Sym2 (ZMod L × ZMod L) :=
  ons_portEdge L ((x, (-1 : ZMod L)), 1)

theorem ons_xSeamPortEdge_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_xSeamPortEdge L) := by
  intro y z h
  have hd := (ons_portEdge_eq_iff L
    (((-1 : ZMod L), z), 0)
    (((-1 : ZMod L), y), 0)).mp h
  rcases hd with hd | hd
  · exact congrArg (fun d : ons_Dart L => d.1.2) hd
  · have hdir := congrArg (fun d : ons_Dart L => d.2) hd
    simp [ons_dartRev] at hdir

theorem ons_ySeamPortEdge_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_ySeamPortEdge L) := by
  intro x z h
  have hd := (ons_portEdge_eq_iff L
    ((z, (-1 : ZMod L)), 1)
    ((x, (-1 : ZMod L)), 1)).mp h
  rcases hd with hd | hd
  · exact congrArg (fun d : ons_Dart L => d.1.1) hd
  · have hdir := congrArg (fun d : ons_Dart L => d.2) hd
    simp [ons_dartRev] at hdir

@[simp] theorem ons_xSeamEdge_xSeamPortEdge
    (L : ℕ) (y : ZMod L) :
    ons_xSeamEdge L (ons_xSeamPortEdge L y) := by
  refine ⟨y, ?_⟩
  simp [ons_xSeamPortEdge, ons_portEdge, ons_dirStep]

@[simp] theorem ons_ySeamEdge_ySeamPortEdge
    (L : ℕ) (x : ZMod L) :
    ons_ySeamEdge L (ons_ySeamPortEdge L x) := by
  refine ⟨x, ?_⟩
  simp [ons_ySeamPortEdge, ons_portEdge, ons_dirStep]

theorem ons_filter_xSeam_eq_image
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    F.filter (ons_xSeamEdge L) =
      (Finset.univ.filter
        (fun y : ZMod L => ons_xSeamPortEdge L y ∈ F)).image
          (ons_xSeamPortEdge L) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hedge, y, rfl⟩
    refine ⟨y, ?_, ?_⟩
    · rw [show ons_xSeamPortEdge L y =
        s(((0 : ZMod L), y), ((-1 : ZMod L), y)) by
          simp [ons_xSeamPortEdge, ons_portEdge, ons_dirStep]]
      exact hedge
    · simp [ons_xSeamPortEdge, ons_portEdge, ons_dirStep]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, ons_xSeamEdge_xSeamPortEdge L y⟩

theorem ons_filter_ySeam_eq_image
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    F.filter (ons_ySeamEdge L) =
      (Finset.univ.filter
        (fun x : ZMod L => ons_ySeamPortEdge L x ∈ F)).image
          (ons_ySeamPortEdge L) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hedge, x, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · rw [show ons_ySeamPortEdge L x =
        s((x, (0 : ZMod L)), (x, (-1 : ZMod L))) by
          simp [ons_ySeamPortEdge, ons_portEdge, ons_dirStep]]
      exact hedge
    · simp [ons_ySeamPortEdge, ons_portEdge, ons_dirStep]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, ons_ySeamEdge_ySeamPortEdge L x⟩

theorem ons_xFlux_neg_one_eq_seamCard
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ons_xFlux F (-1) =
      ((F.filter (ons_xSeamEdge L)).card : ZMod 2) := by
  classical
  unfold ons_xFlux
  calc
    (∑ y : ZMod L, ons_horizontalZBit F (-1, y)) =
        ∑ y : ZMod L,
          if ons_xSeamPortEdge L y ∈ F then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [ons_horizontalZBit, ons_horizontalBit, ons_edgeBit,
        ons_xSeamPortEdge]
      split <;> rfl
    _ = (((Finset.univ : Finset (ZMod L)).filter
          (fun y => ons_xSeamPortEdge L y ∈ F)).card : ZMod 2) := by
      simpa using (Finset.sum_boole
        (R := ZMod 2) (fun y : ZMod L => ons_xSeamPortEdge L y ∈ F)
        Finset.univ)
    _ = ((F.filter (ons_xSeamEdge L)).card : ZMod 2) := by
      rw [ons_filter_xSeam_eq_image L F,
        Finset.card_image_iff.mpr (ons_xSeamPortEdge_injective L).injOn]

theorem ons_yFlux_neg_one_eq_seamCard
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ons_yFlux F (-1) =
      ((F.filter (ons_ySeamEdge L)).card : ZMod 2) := by
  classical
  unfold ons_yFlux
  calc
    (∑ x : ZMod L, ons_verticalZBit F (x, -1)) =
        ∑ x : ZMod L,
          if ons_ySeamPortEdge L x ∈ F then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [ons_verticalZBit, ons_verticalBit, ons_edgeBit,
        ons_ySeamPortEdge]
      split <;> rfl
    _ = (((Finset.univ : Finset (ZMod L)).filter
          (fun x => ons_ySeamPortEdge L x ∈ F)).card : ZMod 2) := by
      simpa using (Finset.sum_boole
        (R := ZMod 2) (fun x : ZMod L => ons_ySeamPortEdge L x ∈ F)
        Finset.univ)
    _ = ((F.filter (ons_ySeamEdge L)).card : ZMod 2) := by
      rw [ons_filter_ySeam_eq_image L F,
        Finset.card_image_iff.mpr (ons_ySeamPortEdge_injective L).injOn]

theorem ons_evenHomology_fst_cast_eq_xFlux
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((ons_evenHomology L F).1 : ZMod 2) = ons_xFlux F (-1) := by
  rw [ons_xFlux_neg_one_eq_seamCard]
  apply ZMod.val_injective 2
  rfl

theorem ons_evenHomology_snd_cast_eq_yFlux
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((ons_evenHomology L F).2 : ZMod 2) = ons_yFlux F (-1) := by
  rw [ons_yFlux_neg_one_eq_seamCard]
  apply ZMod.val_injective 2
  rfl

theorem ons_sum_range_succ_first
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f i =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ∑ i ∈ Finset.range (n + 1 + 1), f i =
            (∑ i ∈ Finset.range (n + 1), f i) + f (n + 1) := by
          rw [Finset.sum_range_succ]
        _ = (f 0 + ∑ i ∈ Finset.range n, f (i + 1)) + f (n + 1) := by
          rw [ih]
        _ = f 0 + ∑ i ∈ Finset.range (n + 1), f (i + 1) := by
          rw [Finset.sum_range_succ]
          abel

theorem ons_sum_zmod_eq_sum_range
    {A : Type*} [AddCommMonoid A]
    (L : ℕ) [NeZero L] (f : ZMod L → A) :
    ∑ z : ZMod L, f z =
      ∑ i ∈ Finset.range L, f (i : ZMod L) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  change (∑ z : Fin (q + 1), f z) = _
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  apply congrArg f
  apply Fin.ext
  change i = i % (q + 1)
  exact (Nat.mod_eq_of_lt (Finset.mem_range.mp hi)).symm

noncomputable def ons_zmodPrefix
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [NeZero L] (f : ZMod L → A) (z : ZMod L) : A :=
  ∑ i ∈ Finset.range z.val, f ((i + 1 : ℕ) : ZMod L)

@[simp] theorem ons_zmodPrefix_zero
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [NeZero L] (f : ZMod L → A) :
    ons_zmodPrefix f 0 = 0 := by
  simp [ons_zmodPrefix]

theorem ons_zmodPrefix_add_one
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → A)
    (z : ZMod L) (hz : z ≠ -1) :
    ons_zmodPrefix f (z + 1) = ons_zmodPrefix f z + f (z + 1) := by
  letI : Fact (1 < L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  have hv : z.val + 1 < L := by
    have hne : z.val ≠ L - 1 := by
      intro h
      apply hz
      apply ZMod.val_injective L
      rw [h, ons_zmod_val_neg_one]
    have := z.val_lt
    omega
  have hval : (z + 1).val = z.val + 1 := by
    rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
  have hcast : (((z.val + 1 : ℕ) : ZMod L)) = z + 1 := by
    apply ZMod.val_injective L
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv, hval]
  unfold ons_zmodPrefix
  rw [hval, Finset.sum_range_succ, hcast]

theorem ons_zmodPrefix_eq_add_pred
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → A)
    (z : ZMod L) (hz : z ≠ 0) :
    ons_zmodPrefix f z = ons_zmodPrefix f (z - 1) + f z := by
  have hpred : z - 1 ≠ -1 := by
    intro h
    apply hz
    calc
      z = (z - 1) + 1 := by ring
      _ = -1 + 1 := by rw [h]
      _ = 0 := by ring
  simpa only [sub_add_cancel] using
    ons_zmodPrefix_add_one f (z - 1) hpred

theorem ons_zmodPrefix_neg_one_of_sum_zero
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → ZMod 2)
    (hsum : ∑ z, f z = 0) :
    ons_zmodPrefix f (-1) = f 0 := by
  have hL : L = (L - 1) + 1 := by
    have := (Fact.out : 2 < L)
    omega
  have hrange := ons_sum_zmod_eq_sum_range L f
  have hdecomp :
      (∑ i ∈ Finset.range L, f (i : ZMod L)) =
        f 0 + ∑ i ∈ Finset.range (L - 1),
          f ((i + 1 : ℕ) : ZMod L) := by
    have hrangeEq : Finset.range L = Finset.range ((L - 1) + 1) := by
      exact congrArg Finset.range hL
    rw [hrangeEq]
    simpa only [Nat.cast_zero] using
      ons_sum_range_succ_first (fun i : ℕ => f (i : ZMod L)) (L - 1)
  rw [hdecomp] at hrange
  have hprefix :
      (∑ i ∈ Finset.range (L - 1), f (↑(i + 1) : ZMod L)) =
        ons_zmodPrefix f (-1) := by
    unfold ons_zmodPrefix
    rw [ons_zmod_val_neg_one]
  rw [hprefix] at hrange
  rw [hsum] at hrange
  have hzero : f 0 + ons_zmodPrefix f (-1) = 0 := hrange.symm
  exact (eq_neg_of_add_eq_zero_right hzero).trans (CharTwo.neg_eq _)

theorem ons_zmod_eq_neg_one_of_eq_pred
    {A : Type*} {L : ℕ} [Fact (2 < L)]
    (f : ZMod L → A) (hpred : ∀ z, f z = f (z - 1))
    (z : ZMod L) :
    f z = f (-1) := by
  have hnat : ∀ n : ℕ, n < L → f (n : ZMod L) = f 0 := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero]
    | succ n ih =>
        have hstep := hpred ((n + 1 : ℕ) : ZMod L)
        have hsub : (((n + 1 : ℕ) : ZMod L) - 1) = (n : ZMod L) := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        rw [hsub] at hstep
        exact hstep.trans (ih (by omega))
  calc
    f z = f (z.val : ZMod L) := by rw [ZMod.natCast_zmod_val]
    _ = f 0 := hnat z.val z.val_lt
    _ = f (-1) := by simpa only [zero_sub] using hpred 0

theorem ons_xFlux_eq_neg_one
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (x : ZMod L) :
    ons_xFlux F x = ons_xFlux F (-1) := by
  exact ons_zmod_eq_neg_one_of_eq_pred
    (ons_xFlux F) (ons_xFlux_pred L F hF) x

theorem ons_yFlux_eq_neg_one
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (y : ZMod L) :
    ons_yFlux F y = ons_yFlux F (-1) := by
  exact ons_zmod_eq_neg_one_of_eq_pred
    (ons_yFlux F) (ons_yFlux_pred L F hF) y

theorem ons_zmodPrefix_add_pred_of_sum_zero
    {L : ℕ} [Fact (2 < L)] (f : ZMod L → ZMod 2)
    (hsum : ∑ z, f z = 0) (z : ZMod L) :
    ons_zmodPrefix f z + ons_zmodPrefix f (z - 1) = f z := by
  by_cases hz : z = 0
  · subst z
    rw [zero_sub, ons_zmodPrefix_zero,
      ons_zmodPrefix_neg_one_of_sum_zero f hsum, zero_add]
  · rw [ons_zmodPrefix_eq_add_pred f z hz]
    calc
      (ons_zmodPrefix f (z - 1) + f z) +
          ons_zmodPrefix f (z - 1) =
          (ons_zmodPrefix f (z - 1) +
            ons_zmodPrefix f (z - 1)) + f z := by abel
      _ = f z := by rw [CharTwo.add_self_eq_zero, zero_add]

noncomputable def ons_zeroFluxHorizontal
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_horizontalZBit F p +
    if p.2 = 0 then ons_xFlux F (-1) else 0

noncomputable def ons_zeroFluxVertical
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_verticalZBit F p +
    if p.1 = 0 then ons_yFlux F (-1) else 0

theorem ons_zeroFlux_divergence_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_zeroFluxHorizontal F p +
      ons_zeroFluxHorizontal F (p.1 - 1, p.2) +
    ons_zeroFluxVertical F p +
      ons_zeroFluxVertical F (p.1, p.2 - 1) = 0 := by
  have hdiv := ons_edgeZBits_divergence_zero L F hF p
  have hx :
      (if p.2 = 0 then ons_xFlux F (-1) else 0) +
        (if p.2 = 0 then ons_xFlux F (-1) else 0) = 0 :=
    CharTwo.add_self_eq_zero _
  have hy :
      (if p.1 = 0 then ons_yFlux F (-1) else 0) +
        (if p.1 = 0 then ons_yFlux F (-1) else 0) = 0 :=
    CharTwo.add_self_eq_zero _
  unfold ons_zeroFluxHorizontal ons_zeroFluxVertical
  linear_combination hdiv + hx + hy

theorem ons_zeroFluxHorizontal_sum_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (x : ZMod L) :
    ∑ y : ZMod L, ons_zeroFluxHorizontal F (x, y) = 0 := by
  unfold ons_zeroFluxHorizontal
  rw [Finset.sum_add_distrib]
  change ons_xFlux F x +
    (∑ y : ZMod L, if y = 0 then ons_xFlux F (-1) else 0) = 0
  rw [ons_xFlux_eq_neg_one L F hF x]
  simp
  exact CharTwo.add_self_eq_zero _

theorem ons_zeroFluxVertical_sum_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (y : ZMod L) :
    ∑ x : ZMod L, ons_zeroFluxVertical F (x, y) = 0 := by
  unfold ons_zeroFluxVertical
  rw [Finset.sum_add_distrib]
  change ons_yFlux F y +
    (∑ x : ZMod L, if x = 0 then ons_yFlux F (-1) else 0) = 0
  rw [ons_yFlux_eq_neg_one L F hF y]
  simp
  exact CharTwo.add_self_eq_zero _

noncomputable def ons_zeroFluxPotential
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_zmodPrefix (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
    ons_zmodPrefix (fun x ↦ ons_zeroFluxVertical F (x, p.2)) p.1

theorem ons_zeroFluxPotential_vertical_boundary
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_zeroFluxPotential F p +
      ons_zeroFluxPotential F (p.1 - 1, p.2) =
        ons_zeroFluxVertical F p := by
  have hv := ons_zmodPrefix_add_pred_of_sum_zero
    (fun x ↦ ons_zeroFluxVertical F (x, p.2))
    (ons_zeroFluxVertical_sum_zero L F hF p.2) p.1
  unfold ons_zeroFluxPotential
  calc
    (ons_zmodPrefix
          (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
        ons_zmodPrefix
          (fun x ↦ ons_zeroFluxVertical F (x, p.2)) p.1) +
      (ons_zmodPrefix
          (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
        ons_zmodPrefix
          (fun x ↦ ons_zeroFluxVertical F (x, p.2)) (p.1 - 1)) =
        (ons_zmodPrefix
            (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
          ons_zmodPrefix
            (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2) +
        (ons_zmodPrefix
            (fun x ↦ ons_zeroFluxVertical F (x, p.2)) p.1 +
          ons_zmodPrefix
            (fun x ↦ ons_zeroFluxVertical F (x, p.2)) (p.1 - 1)) := by
          abel
    _ = ons_zeroFluxVertical F p := by
      rw [CharTwo.add_self_eq_zero, zero_add, hv]

theorem ons_zeroFluxPotential_horizontal_boundary
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_zeroFluxPotential F p +
      ons_zeroFluxPotential F (p.1, p.2 - 1) =
        ons_zeroFluxHorizontal F p := by
  have hnat : ∀ n : ℕ, n < L →
      ons_zeroFluxPotential F ((n : ZMod L), p.2) +
        ons_zeroFluxPotential F ((n : ZMod L), p.2 - 1) =
          ons_zeroFluxHorizontal F ((n : ZMod L), p.2) := by
    intro n hn
    induction n with
    | zero =>
        have hh := ons_zmodPrefix_add_pred_of_sum_zero
          (fun y ↦ ons_zeroFluxHorizontal F (0, y))
          (ons_zeroFluxHorizontal_sum_zero L F hF 0) p.2
        simpa only [Nat.cast_zero, ons_zeroFluxPotential,
          ons_zmodPrefix_zero, add_zero] using hh
    | succ n ih =>
        have hn : n < L := by omega
        have hnneg : (n : ZMod L) ≠ -1 := by
          intro heq
          have hval := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt hn, ons_zmod_val_neg_one] at hval
          omega
        have hcast : ((n + 1 : ℕ) : ZMod L) = (n : ZMod L) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        have hv := ons_zmodPrefix_add_one
          (fun x ↦ ons_zeroFluxVertical F (x, p.2))
          (n : ZMod L) hnneg
        have hvpred := ons_zmodPrefix_add_one
          (fun x ↦ ons_zeroFluxVertical F (x, p.2 - 1))
          (n : ZMod L) hnneg
        have hsub : (((n + 1 : ℕ) : ZMod L) - 1) =
            (n : ZMod L) := by
          rw [hcast]
          ring
        have hdiv := ons_zeroFlux_divergence_zero L F hF
          (((n + 1 : ℕ) : ZMod L), p.2)
        rw [hsub] at hdiv
        have hstep :
            ons_zeroFluxHorizontal F ((n : ZMod L), p.2) +
              ons_zeroFluxVertical F (((n + 1 : ℕ) : ZMod L), p.2) +
              ons_zeroFluxVertical F
                (((n + 1 : ℕ) : ZMod L), p.2 - 1) =
              ons_zeroFluxHorizontal F
                (((n + 1 : ℕ) : ZMod L), p.2) := by
          have hzero :
              (ons_zeroFluxHorizontal F ((n : ZMod L), p.2) +
                ons_zeroFluxVertical F
                  (((n + 1 : ℕ) : ZMod L), p.2) +
                ons_zeroFluxVertical F
                  (((n + 1 : ℕ) : ZMod L), p.2 - 1)) +
                ons_zeroFluxHorizontal F
                  (((n + 1 : ℕ) : ZMod L), p.2) = 0 := by
            linear_combination hdiv
          exact (eq_neg_of_add_eq_zero_left hzero).trans
            (CharTwo.neg_eq _)
        rw [hcast]
        unfold ons_zeroFluxPotential
        rw [hv, hvpred]
        calc
          (ons_zmodPrefix
                (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
              (ons_zmodPrefix
                  (fun x ↦ ons_zeroFluxVertical F (x, p.2))
                    (n : ZMod L) +
                ons_zeroFluxVertical F
                  ((n : ZMod L) + 1, p.2))) +
            (ons_zmodPrefix
                (fun y ↦ ons_zeroFluxHorizontal F (0, y))
                  (p.2 - 1) +
              (ons_zmodPrefix
                  (fun x ↦ ons_zeroFluxVertical F (x, p.2 - 1))
                    (n : ZMod L) +
                ons_zeroFluxVertical F
                  ((n : ZMod L) + 1, p.2 - 1))) =
              (ons_zeroFluxPotential F ((n : ZMod L), p.2) +
                ons_zeroFluxPotential F ((n : ZMod L), p.2 - 1)) +
              ons_zeroFluxVertical F ((n : ZMod L) + 1, p.2) +
              ons_zeroFluxVertical F
                ((n : ZMod L) + 1, p.2 - 1) := by
                  unfold ons_zeroFluxPotential
                  abel
          _ = ons_zeroFluxHorizontal F
                ((n : ZMod L) + 1, p.2) := by
            rw [ih hn]
            rw [hcast] at hstep
            exact hstep
  simpa only [ZMod.natCast_zmod_val] using hnat p.1.val p.1.val_lt

theorem ons_zeroFlux_intersection_eq_zero
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
    (∑ p : ZMod L × ZMod L,
      (ons_zeroFluxHorizontal F p *
          ons_verticalZBit G (p.1, p.2 - 1) +
        ons_zeroFluxVertical F p *
          ons_horizontalZBit G (p.1 - 1, p.2))) = 0 := by
  have hvshift :
      (∑ p : ZMod L × ZMod L,
        ons_zeroFluxPotential F (p.1, p.2 - 1) *
          ons_verticalZBit G (p.1, p.2 - 1)) =
        ∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_verticalZBit G p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.refl (ZMod L))
          (Equiv.addRight (-1 : ZMod L)))
        (fun p : ZMod L × ZMod L ↦
          ons_zeroFluxPotential F p * ons_verticalZBit G p))
  have hhshift :
      (∑ p : ZMod L × ZMod L,
        ons_zeroFluxPotential F (p.1 - 1, p.2) *
          ons_horizontalZBit G (p.1 - 1, p.2)) =
        ∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_horizontalZBit G p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight (-1 : ZMod L))
          (Equiv.refl (ZMod L)))
        (fun p : ZMod L × ZMod L ↦
          ons_zeroFluxPotential F p * ons_horizontalZBit G p))
  simp_rw [← ons_zeroFluxPotential_horizontal_boundary L F hF,
    ← ons_zeroFluxPotential_vertical_boundary L F hF, add_mul]
  calc
    (∑ p : ZMod L × ZMod L,
      (ons_zeroFluxPotential F p *
          ons_verticalZBit G (p.1, p.2 - 1) +
        ons_zeroFluxPotential F (p.1, p.2 - 1) *
          ons_verticalZBit G (p.1, p.2 - 1) +
        (ons_zeroFluxPotential F p *
            ons_horizontalZBit G (p.1 - 1, p.2) +
          ons_zeroFluxPotential F (p.1 - 1, p.2) *
            ons_horizontalZBit G (p.1 - 1, p.2)))) =
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F (p.1, p.2 - 1) *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_horizontalZBit G (p.1 - 1, p.2)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F (p.1 - 1, p.2) *
            ons_horizontalZBit G (p.1 - 1, p.2)) := by
          simp only [Finset.sum_add_distrib]
          abel
    _ =
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_verticalZBit G p) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p *
            ons_horizontalZBit G (p.1 - 1, p.2)) +
        (∑ p : ZMod L × ZMod L,
          ons_zeroFluxPotential F p * ons_horizontalZBit G p) := by
          rw [hvshift, hhshift]
    _ = ∑ p : ZMod L × ZMod L,
        ons_zeroFluxPotential F p *
          (ons_horizontalZBit G p +
            ons_horizontalZBit G (p.1 - 1, p.2) +
            ons_verticalZBit G p +
            ons_verticalZBit G (p.1, p.2 - 1)) := by
          simp only [mul_add, Finset.sum_add_distrib]
          abel
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      rw [ons_edgeZBits_divergence_zero L G hG p, mul_zero]

noncomputable def ons_edgeCycleZIntersection
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) : ZMod 2 :=
  ∑ p : ZMod L × ZMod L,
    (ons_horizontalZBit F p *
        ons_verticalZBit G (p.1, p.2 - 1) +
      ons_verticalZBit F p *
        ons_horizontalZBit G (p.1 - 1, p.2))

theorem ons_horizontalZBit_eq_zeroFlux_add
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) :
    ons_horizontalZBit F p =
      ons_zeroFluxHorizontal F p +
        if p.2 = 0 then ons_xFlux F (-1) else 0 := by
  unfold ons_zeroFluxHorizontal
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem ons_verticalZBit_eq_zeroFlux_add
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) :
    ons_verticalZBit F p =
      ons_zeroFluxVertical F p +
        if p.1 = 0 then ons_yFlux F (-1) else 0 := by
  unfold ons_zeroFluxVertical
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem ons_horizontalSeam_intersection_sum
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (∑ p : ZMod L × ZMod L,
      (if p.2 = 0 then ons_xFlux F (-1) else 0) *
        ons_verticalZBit G (p.1, p.2 - 1)) =
      ons_xFlux F (-1) * ons_yFlux G (-1) := by
  calc
    (∑ p : ZMod L × ZMod L,
      (if p.2 = 0 then ons_xFlux F (-1) else 0) *
        ons_verticalZBit G (p.1, p.2 - 1)) =
        ∑ x : ZMod L,
          ons_xFlux F (-1) * ons_verticalZBit G (x, -1) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = ons_xFlux F (-1) * ons_yFlux G (-1) := by
      unfold ons_yFlux
      rw [Finset.mul_sum]

theorem ons_verticalSeam_intersection_sum
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (∑ p : ZMod L × ZMod L,
      (if p.1 = 0 then ons_yFlux F (-1) else 0) *
        ons_horizontalZBit G (p.1 - 1, p.2)) =
      ons_yFlux F (-1) * ons_xFlux G (-1) := by
  calc
    (∑ p : ZMod L × ZMod L,
      (if p.1 = 0 then ons_yFlux F (-1) else 0) *
        ons_horizontalZBit G (p.1 - 1, p.2)) =
        ∑ y : ZMod L,
          ons_yFlux F (-1) * ons_horizontalZBit G (-1, y) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = ons_yFlux F (-1) * ons_xFlux G (-1) := by
      unfold ons_xFlux
      rw [Finset.mul_sum]

theorem ons_edgeCycleZIntersection_eq_flux
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
    ons_edgeCycleZIntersection F G =
      ons_xFlux F (-1) * ons_yFlux G (-1) +
        ons_yFlux F (-1) * ons_xFlux G (-1) := by
  unfold ons_edgeCycleZIntersection
  have hH : ∀ p : ZMod L × ZMod L, ons_horizontalZBit F p =
      ons_zeroFluxHorizontal F p +
        if p.2 = 0 then ons_xFlux F (-1) else 0 :=
    ons_horizontalZBit_eq_zeroFlux_add F
  have hV : ∀ p : ZMod L × ZMod L, ons_verticalZBit F p =
      ons_zeroFluxVertical F p +
        if p.1 = 0 then ons_yFlux F (-1) else 0 :=
    ons_verticalZBit_eq_zeroFlux_add F
  simp_rw [hH, hV]
  calc
    (∑ p : ZMod L × ZMod L,
      ((ons_zeroFluxHorizontal F p +
            if p.2 = 0 then ons_xFlux F (-1) else 0) *
          ons_verticalZBit G (p.1, p.2 - 1) +
        (ons_zeroFluxVertical F p +
            if p.1 = 0 then ons_yFlux F (-1) else 0) *
          ons_horizontalZBit G (p.1 - 1, p.2))) =
        (∑ p : ZMod L × ZMod L,
          (ons_zeroFluxHorizontal F p *
              ons_verticalZBit G (p.1, p.2 - 1) +
            ons_zeroFluxVertical F p *
              ons_horizontalZBit G (p.1 - 1, p.2))) +
        (∑ p : ZMod L × ZMod L,
          (if p.2 = 0 then ons_xFlux F (-1) else 0) *
            ons_verticalZBit G (p.1, p.2 - 1)) +
        (∑ p : ZMod L × ZMod L,
          (if p.1 = 0 then ons_yFlux F (-1) else 0) *
            ons_horizontalZBit G (p.1 - 1, p.2)) := by
          simp only [add_mul, Finset.sum_add_distrib]
          abel
    _ = ons_xFlux F (-1) * ons_yFlux G (-1) +
          ons_yFlux F (-1) * ons_xFlux G (-1) := by
      rw [ons_zeroFlux_intersection_eq_zero L F G hF hG,
        ons_horizontalSeam_intersection_sum L F G,
        ons_verticalSeam_intersection_sum L F G, zero_add]

theorem ons_edgeCycleIntersection_cast
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (ons_edgeCycleIntersection F G : ZMod 2) =
      ons_edgeCycleZIntersection F G := by
  unfold ons_edgeCycleIntersection ons_edgeCycleZIntersection
  rfl

theorem ons_homologyIntersection_cast_eq_flux
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) :
    (ons_homologyIntersection
        (ons_evenHomology L F) (ons_evenHomology L G) : ZMod 2) =
      ons_xFlux F (-1) * ons_yFlux G (-1) +
        ons_yFlux F (-1) * ons_xFlux G (-1) := by
  unfold ons_homologyIntersection
  rw [ons_evenHomology_fst_cast_eq_xFlux L F,
    ons_evenHomology_snd_cast_eq_yFlux L F,
    ons_evenHomology_fst_cast_eq_xFlux L G,
    ons_evenHomology_snd_cast_eq_yFlux L G]
  rfl

theorem ons_edgeCycleIntersection_eq_homologyIntersection
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
    ons_edgeCycleIntersection F G =
      ons_homologyIntersection
        (ons_evenHomology L F) (ons_evenHomology L G) := by
  have hz :
      (ons_edgeCycleIntersection F G : ZMod 2) =
        (ons_homologyIntersection
          (ons_evenHomology L F) (ons_evenHomology L G) : ZMod 2) := by
    have hcast := ons_edgeCycleIntersection_cast F G
    have hflux := ons_edgeCycleZIntersection_eq_flux L F G hF hG
    have hhom := ons_homologyIntersection_cast_eq_flux L F G
    exact hcast.trans (hflux.trans hhom.symm)
  exact_mod_cast hz

theorem ons_walk_edges_incCount_eq_zero_of_not_mem_support
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (z : V)
    (hz : z ∉ p.support) :
    incCount p.edges.toFinset z = 0 := by
  unfold incCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro edge hedge hzedge
  apply hz
  exact p.mem_support_of_mem_edges (List.mem_toFinset.mp hedge) hzedge

theorem ons_walk_edges_incCounts_disjoint_of_support_disjoint
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v x y : V} (p : G.Walk u v) (q : G.Walk x y)
    (hdisj : List.Disjoint p.support q.support) :
    ∀ z, incCount p.edges.toFinset z = 0 ∨
      incCount q.edges.toFinset z = 0 := by
  intro z
  by_cases hz : z ∈ p.support
  · right
    apply ons_walk_edges_incCount_eq_zero_of_not_mem_support q z
    intro hzq
    exact (List.disjoint_left.mp hdisj) hz hzq
  · left
    exact ons_walk_edges_incCount_eq_zero_of_not_mem_support p z hz

theorem ons_homologyIntersection_eq_zero_of_incCount_disjoint
    (L : ℕ) [Fact (2 < L)]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (hG : G ∈ evenSubgraphs (onsTorusGraph L))
    (hdisj : ∀ p, incCount F p = 0 ∨ incCount G p = 0) :
    ons_homologyIntersection
      (ons_evenHomology L F) (ons_evenHomology L G) = 0 := by
  rw [← ons_edgeCycleIntersection_eq_homologyIntersection L F G hF hG]
  exact ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint F G hdisj

theorem ons_decEmbedWalk_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hqsnd : q.snd = ons_dartRev L d)
    (hpsnd : p.snd = ons_dartRev L e)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
    ons_homologyIntersection
      (ons_evenHomology L (ons_walkOriginalEdges q))
      (ons_evenHomology L (ons_walkOriginalEdges p)) = 0 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  have hqeven : (ons_decEmbedWalk L q).edges.toFinset ∈
      evenSubgraphs (onsTorusGraph (8 * L)) :=
    ons_cycle_edges_evenSubgraph (onsTorusGraph (8 * L))
      (ons_decEmbedWalk L q)
      (ons_decEmbedWalk_isCycle L q hq)
  have hpeven : (ons_decEmbedWalk L p).edges.toFinset ∈
      evenSubgraphs (onsTorusGraph (8 * L)) :=
    ons_cycle_edges_evenSubgraph (onsTorusGraph (8 * L))
      (ons_decEmbedWalk L p)
      (ons_decEmbedWalk_isCycle L p hp)
  have hsupp :=
    ons_decEmbedWalk_support_disjoint_of_toSubgraph L q p hdisj
  have hrefined :
      ons_homologyIntersection
        (ons_evenHomology (8 * L) (ons_decEmbedWalk L q).edges.toFinset)
        (ons_evenHomology (8 * L) (ons_decEmbedWalk L p).edges.toFinset) = 0 :=
    ons_homologyIntersection_eq_zero_of_incCount_disjoint
      (8 * L) _ _ hqeven hpeven
      (ons_walk_edges_incCounts_disjoint_of_support_disjoint
        (ons_decEmbedWalk L q) (ons_decEmbedWalk L p) hsupp)
  rw [ons_decEmbedWalk_evenHomology_eq L q hq hqsnd,
    ons_decEmbedWalk_evenHomology_eq L p hp hpsnd] at hrefined
  exact hrefined

theorem ons_decCycles_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
    ons_homologyIntersection
      (ons_evenHomology L (ons_walkOriginalEdges q))
      (ons_evenHomology L (ons_walkOriginalEdges p)) = 0 := by
  obtain ⟨dq, q', hq', hqsnd, hqedges⟩ :=
    ons_decCycle_root_external q hq
  obtain ⟨dp, p', hp', hpsnd, hpedges⟩ :=
    ons_decCycle_root_external p hp
  have hqverts : q'.toSubgraph.verts = q.toSubgraph.verts := by
    ext z
    rw [q'.mem_verts_toSubgraph, q.mem_verts_toSubgraph,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hq'.not_nil,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hq.not_nil]
    constructor
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hqedges.symm ▸ List.mem_toFinset.mpr hedge)
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hqedges ▸ List.mem_toFinset.mpr hedge)
  have hpverts : p'.toSubgraph.verts = p.toSubgraph.verts := by
    ext z
    rw [p'.mem_verts_toSubgraph, p.mem_verts_toSubgraph,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp'.not_nil,
      SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil]
    constructor
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hpedges.symm ▸ List.mem_toFinset.mpr hedge)
    · rintro ⟨edge, hedge, hzedge⟩
      refine ⟨edge, ?_, hzedge⟩
      exact List.mem_toFinset.mp
        (hpedges ▸ List.mem_toFinset.mpr hedge)
  have hrootDisj : Disjoint q'.toSubgraph.verts p'.toSubgraph.verts := by
    rw [hqverts, hpverts]
    exact hdisj
  have hroot := ons_decEmbedWalk_originalHomology_isotropic
    L q' p' hq' hp' hqsnd hpsnd hrootDisj
  have hqorig : ons_walkOriginalEdges q' = ons_walkOriginalEdges q := by
    unfold ons_walkOriginalEdges ons_walkExternalEdges
    rw [hqedges]
  have hporig : ons_walkOriginalEdges p' = ons_walkOriginalEdges p := by
    unfold ons_walkOriginalEdges ons_walkExternalEdges
    rw [hpedges]
  rwa [hqorig, hporig] at hroot

theorem ons_decCycleFamily_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : ι → ons_Dart L)
    (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i))
    (hcycle : ∀ i, (p i).IsCycle)
    (hverts : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i ↦ (p i).toSubgraph.verts)) :
    ∀ i j, i ≠ j →
      ons_homologyIntersection
        (ons_evenHomology L (ons_walkOriginalEdges (p i)))
        (ons_evenHomology L (ons_walkOriginalEdges (p j))) = 0 := by
  intro i j hij
  apply ons_decCycles_originalHomology_isotropic L
    (p i) (p j) (hcycle i) (hcycle j)
  exact hverts (Finset.mem_univ i) (Finset.mem_univ j) hij

end StatMech.Onsager
