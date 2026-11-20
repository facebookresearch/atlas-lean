/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalUnequalBridgeGeometry
import Code.Ising.GHSLebowitz
import Code.Ising.IsingFKGLayer
import Code.Ising.RectangularPrismTransfer










namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness
open Matrix
open scoped BigOperators

noncomputable section



def oddPrismLowerBlockSiteEquiv (n : Nat) :
    OddPrismLowerBlockSite n ≃
      Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (n + 1) where
  toFun v := (v.1.x, v.1.y, ⟨v.1.z.val, by
    have hz := v.2
    unfold oddPrismAtOrBelowCenter at hz
    omega⟩)
  invFun p := ⟨⟨p.1, p.2.1, ⟨p.2.2.val, by omega⟩⟩, by
    unfold oddPrismAtOrBelowCenter
    have hz := p.2.2.isLt
    change p.2.2.val <= n
    omega⟩
  left_inv v := by
    apply Subtype.ext
    cases v.1
    rfl
  right_inv p := by
    rcases p with ⟨x, y, z⟩
    rfl



def oddPrismUpperBlockReflectedSiteEquiv (n : Nat) :
    OddPrismUpperBlockSite n ≃
      Fin (2 * n + 1) × Fin (2 * n + 1) × Fin n where
  toFun v := (v.1.x, v.1.y, ⟨2 * n - v.1.z.val, by
    have hzUpper := v.2
    have hzLt := v.1.z.isLt
    unfold oddPrismAtOrBelowCenter at hzUpper
    omega⟩)
  invFun p := ⟨⟨p.1, p.2.1, ⟨2 * n - p.2.2.val, by
    have hk := p.2.2.isLt
    omega⟩⟩, by
    have hk := p.2.2.isLt
    unfold oddPrismAtOrBelowCenter
    change ¬2 * n - p.2.2.val <= n
    omega⟩
  left_inv v := by
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases v with
      | mk x y z =>
        have hzLt := z.isLt
        simp only
        congr
        omega
  right_inv p := by
    rcases p with ⟨x, y, k⟩
    have hk := k.isLt
    simp only
    congr
    omega


def oddPrismLowerBlockLayer (n : Nat)
    (sigma : ConfigSpace (OddPrismLowerBlockSite n)) (k : Fin (n + 1)) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) :=
  fun p => sigma ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))


def oddPrismUpperBlockReflectedLayer (n : Nat)
    (sigma : ConfigSpace (OddPrismUpperBlockSite n)) (k : Fin n) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) :=
  fun p => sigma
    ((oddPrismUpperBlockReflectedSiteEquiv n).symm (p.1, p.2, k))



def oddPrismLowerBlockLayerEquiv (n : Nat) :
    ConfigSpace (OddPrismLowerBlockSite n) ≃
      (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) where
  toFun := oddPrismLowerBlockLayer n
  invFun q := fun v =>
    q (oddPrismLowerBlockSiteEquiv n v).2.2
      ((oddPrismLowerBlockSiteEquiv n v).1,
        (oddPrismLowerBlockSiteEquiv n v).2.1)
  left_inv sigma := by
    funext v
    change sigma ((oddPrismLowerBlockSiteEquiv n).symm
      (oddPrismLowerBlockSiteEquiv n v)) = sigma v
    rw [Equiv.symm_apply_apply]
  right_inv q := by
    funext k p
    change q
        (oddPrismLowerBlockSiteEquiv n
          ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))).2.2
        ((oddPrismLowerBlockSiteEquiv n
          ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))).1,
          (oddPrismLowerBlockSiteEquiv n
            ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))).2.1) =
      q k p
    rw [Equiv.apply_symm_apply]



def oddPrismUpperBlockReflectedLayerEquiv (n : Nat) :
    ConfigSpace (OddPrismUpperBlockSite n) ≃
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) where
  toFun := oddPrismUpperBlockReflectedLayer n
  invFun q := fun v =>
    q (oddPrismUpperBlockReflectedSiteEquiv n v).2.2
      ((oddPrismUpperBlockReflectedSiteEquiv n v).1,
        (oddPrismUpperBlockReflectedSiteEquiv n v).2.1)
  left_inv sigma := by
    funext v
    change sigma ((oddPrismUpperBlockReflectedSiteEquiv n).symm
      (oddPrismUpperBlockReflectedSiteEquiv n v)) = sigma v
    rw [Equiv.symm_apply_apply]
  right_inv q := by
    funext k p
    change q
        (oddPrismUpperBlockReflectedSiteEquiv n
          ((oddPrismUpperBlockReflectedSiteEquiv n).symm
            (p.1, p.2, k))).2.2
        ((oddPrismUpperBlockReflectedSiteEquiv n
          ((oddPrismUpperBlockReflectedSiteEquiv n).symm
            (p.1, p.2, k))).1,
          (oddPrismUpperBlockReflectedSiteEquiv n
            ((oddPrismUpperBlockReflectedSiteEquiv n).symm
              (p.1, p.2, k))).2.1) = q k p
    rw [Equiv.apply_symm_apply]


def oddPrismUpperSeamLayerIndex (n : Nat) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩


@[simp] theorem oddPrismLowerBlockSiteEquiv_surface
    (n : Nat) (i j : Fin (2 * n + 1)) :
    oddPrismLowerBlockSiteEquiv n (oddPrismLowerHalfSurfaceSite n i j) =
      (i, j, Fin.last n) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl


@[simp] theorem oddPrismUpperBlockReflectedSiteEquiv_surface
    (n : Nat) (hn : 0 < n) (i j : Fin (2 * n + 1)) :
    oddPrismUpperBlockReflectedSiteEquiv n
        (oddPrismUpperHalfSurfaceSite n hn i j) =
      (i, j, oddPrismUpperSeamLayerIndex n hn) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [oddPrismUpperBlockReflectedSiteEquiv,
        oddPrismUpperHalfSurfaceSite, oddPrismUpperSeamLayerIndex]
      omega



theorem spin_oddPrismLowerHalfSurfaceSite_eq_layer
    (n : Nat) (sigma : ConfigSpace (OddPrismLowerBlockSite n))
    (i j : Fin (2 * n + 1)) :
    spin sigma (oddPrismLowerHalfSurfaceSite n i j) =
      spin (oddPrismLowerBlockLayer n sigma (Fin.last n)) (i, j) := by
  unfold oddPrismLowerBlockLayer
  change spin sigma (oddPrismLowerHalfSurfaceSite n i j) =
    spin sigma ((oddPrismLowerBlockSiteEquiv n).symm
      (i, j, Fin.last n))
  have hsite : (oddPrismLowerBlockSiteEquiv n).symm
      (i, j, Fin.last n) = oddPrismLowerHalfSurfaceSite n i j := by
    apply (oddPrismLowerBlockSiteEquiv n).injective
    rw [Equiv.apply_symm_apply]
    exact (oddPrismLowerBlockSiteEquiv_surface n i j).symm
  rw [hsite]



theorem spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer
    (n : Nat) (hn : 0 < n)
    (sigma : ConfigSpace (OddPrismUpperBlockSite n))
    (i j : Fin (2 * n + 1)) :
    spin sigma (oddPrismUpperHalfSurfaceSite n hn i j) =
      spin (oddPrismUpperBlockReflectedLayer n sigma
        (oddPrismUpperSeamLayerIndex n hn))
        (i, j) := by
  unfold oddPrismUpperBlockReflectedLayer
  change spin sigma (oddPrismUpperHalfSurfaceSite n hn i j) =
    spin sigma ((oddPrismUpperBlockReflectedSiteEquiv n).symm
      (i, j, oddPrismUpperSeamLayerIndex n hn))
  have hsite : (oddPrismUpperBlockReflectedSiteEquiv n).symm
      (i, j, oddPrismUpperSeamLayerIndex n hn) =
        oddPrismUpperHalfSurfaceSite n hn i j := by
    apply (oddPrismUpperBlockReflectedSiteEquiv n).injective
    rw [Equiv.apply_symm_apply]
    exact (oddPrismUpperBlockReflectedSiteEquiv_surface n hn i j).symm
  rw [hsite]



theorem oddPrismUnequalBridgeInteraction_eq_layerDotProduct
    (n : Nat) (hn : 0 < n)
    (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n)) :
    unequalReplicaBridgeInteraction
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) a b =
      ∑ p : Fin (2 * n + 1) × Fin (2 * n + 1),
        spin (oddPrismLowerBlockLayer n a (Fin.last n)) p *
          spin (oddPrismUpperBlockReflectedLayer n b
            (oddPrismUpperSeamLayerIndex n hn)) p := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold unequalReplicaBridgeInteraction
  rw [sum_oddPrism_fis_interface n hn]
  apply Finset.sum_congr rfl
  intro p _
  unfold oddPrismCentralInterfaceEdge
  change spin (isingSumConfigEquiv.symm (a, b))
        (Sum.inl (oddPrismLowerHalfSurfaceSite n p.1 p.2)) *
      spin (isingSumConfigEquiv.symm (a, b))
        (Sum.inr (oddPrismUpperHalfSurfaceSite n hn p.1 p.2)) = _
  rw [spin_isingSumConfigEquiv_symm_inl,
    spin_isingSumConfigEquiv_symm_inr]
  rw [spin_oddPrismLowerHalfSurfaceSite_eq_layer,
    spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer]




def oddPrismLayerHalfWeight (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  Real.exp (rectangularLayerBoltzmannInteraction 1 beta s / 2)


def oddPrismUpperTransferTail (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ (n - 1)) *ᵥ
    rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1)


def oddPrismLowerTransferTail (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ n) *ᵥ
    rectangularPrismTransferBoundaryVector 1 beta (2 * n + 1) (2 * n + 1)



def oddPrismUpperConditionedVector (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  fun s => oddPrismLayerHalfWeight beta n s *
    oddPrismUpperTransferTail beta n s


def oddPrismLowerConditionedVector (beta : Real) (n : Nat) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) -> Real :=
  fun s => oddPrismLayerHalfWeight beta n s *
    oddPrismLowerTransferTail beta n s

theorem oddPrismLayerHalfWeight_pos (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismLayerHalfWeight beta n s := by
  exact Real.exp_pos _



theorem oddPrismLowerTransferTail_eq_mulVec_upper
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismLowerTransferTail beta n =
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ
        oddPrismUpperTransferTail beta n := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  funext s
  change ((A ^ n) *ᵥ a) s = (A *ᵥ (A ^ (n - 1)) *ᵥ a) s
  have hpow : A ^ n = A * A ^ (n - 1) := by
    calc
      A ^ n = A ^ ((n - 1) + 1) := by congr 1; omega
      _ = A * A ^ (n - 1) := pow_succ' A (n - 1)
  rw [hpow, ← Matrix.mulVec_mulVec]


theorem oddPrismLowerConditionedVector_eq_transfer_upper
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismLowerConditionedVector beta n = fun s =>
      oddPrismLayerHalfWeight beta n s *
        (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ
          (fun q => oddPrismUpperConditionedVector beta n q /
            oddPrismLayerHalfWeight beta n q)) s := by
  funext s
  unfold oddPrismLowerConditionedVector
  rw [oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]
  congr 1
  congr 1
  funext q
  unfold oddPrismUpperConditionedVector
  rw [mul_div_cancel_left₀]
  exact (oddPrismLayerHalfWeight_pos beta n q).ne'


def oddPrismLayerSeamInteraction (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  ∑ p : Fin (2 * n + 1) × Fin (2 * n + 1),
    spin s p * spin q p



def oddPrismPureSeamKernel (r : Real) (n : Nat) :
    Matrix (RectangularLayerConfig (2 * n + 1) (2 * n + 1))
      (RectangularLayerConfig (2 * n + 1) (2 * n + 1)) Real :=
  fun s q => Real.exp (r * oddPrismLayerSeamInteraction n s q)

theorem oddPrismPureSeamKernel_pos (r : Real) (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismPureSeamKernel r n s q := by
  exact Real.exp_pos _



def oddPrismTiltedSeamTransfer (beta : Real) (n : Nat) (r : Real) :
    Matrix (RectangularLayerConfig (2 * n + 1) (2 * n + 1))
      (RectangularLayerConfig (2 * n + 1) (2 * n + 1)) Real :=
  fun s q => oddPrismLayerHalfWeight beta n s *
    oddPrismPureSeamKernel r n s q * oddPrismLayerHalfWeight beta n q

theorem oddPrismTiltedSeamTransfer_eq_rectangularTransfer
    (beta : Real) (n : Nat) :
    oddPrismTiltedSeamTransfer beta n beta =
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) := by
  funext s q
  unfold oddPrismTiltedSeamTransfer oddPrismLayerHalfWeight
    oddPrismPureSeamKernel oddPrismLayerSeamInteraction
    rectangularPrismTransfer rectangularLayerVerticalInteraction
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring



theorem oddPrismTiltedSeamTransfer_eq_transfer_mul_exp
    (beta : Real) (n : Nat) (r : Real)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTiltedSeamTransfer beta n r s t =
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) s t *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n s t) := by
  unfold oddPrismTiltedSeamTransfer oddPrismLayerHalfWeight
    oddPrismPureSeamKernel rectangularPrismTransfer
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  unfold oddPrismLayerSeamInteraction rectangularLayerVerticalInteraction
  congr 1
  ring




def oddPrismTransferBridgeRawMoment (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n q *
      oddPrismPureSeamKernel r n s q

def oddPrismTransferBridgeRawFirst (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n q *
      (oddPrismLayerSeamInteraction n s q *
        oddPrismPureSeamKernel r n s q)

def oddPrismTransferBridgeRawSecond (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n q *
      (oddPrismLayerSeamInteraction n s q ^ 2 *
        oddPrismPureSeamKernel r n s q)


def oddPrismTransferBridgeVariance (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeRawSecond beta n r /
      oddPrismTransferBridgeRawMoment beta n r -
    (oddPrismTransferBridgeRawFirst beta n r /
      oddPrismTransferBridgeRawMoment beta n r) ^ 2



theorem oddPrismTransferBridgeRawMoment_eq_tailContraction
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ s, oddPrismLowerTransferTail beta n s *
        (oddPrismTiltedSeamTransfer beta n r *ᵥ
          oddPrismUpperTransferTail beta n) s := by
  unfold oddPrismTransferBridgeRawMoment
    oddPrismLowerConditionedVector oddPrismUpperConditionedVector
    oddPrismTiltedSeamTransfer Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring



theorem oddPrismTransferBridgeRawMoment_eq_oneStepContraction
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ s,
        (rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) *ᵥ
          oddPrismUpperTransferTail beta n) s *
        (oddPrismTiltedSeamTransfer beta n r *ᵥ
          oddPrismUpperTransferTail beta n) s := by
  rw [oddPrismTransferBridgeRawMoment_eq_tailContraction]
  rw [oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]


def oddPrismTransferBridgeFlippedRawMoment
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV q) *
      oddPrismPureSeamKernel r n s q

def oddPrismTransferBridgeFlippedRawFirst
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV q) *
      (oddPrismLayerSeamInteraction n s q *
        oddPrismPureSeamKernel r n s q)

def oddPrismTransferBridgeFlippedRawSecond
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ s, ∑ q,
    oddPrismLowerConditionedVector beta n s *
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV q) *
      (oddPrismLayerSeamInteraction n s q ^ 2 *
        oddPrismPureSeamKernel r n s q)

def oddPrismTransferBridgeFlippedVariance
    (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeFlippedRawSecond beta n r /
      oddPrismTransferBridgeFlippedRawMoment beta n r -
    (oddPrismTransferBridgeFlippedRawFirst beta n r /
      oddPrismTransferBridgeFlippedRawMoment beta n r) ^ 2

@[simp] theorem oddPrismLayerSeamInteraction_flip_right
    (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s (FieldGhostDict.flipV q) =
      -oddPrismLayerSeamInteraction n s q := by
  unfold oddPrismLayerSeamInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

@[simp] theorem oddPrismPureSeamKernel_flip_right
    (r : Real) (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n s (FieldGhostDict.flipV q) =
      oddPrismPureSeamKernel (-r) n s q := by
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_flip_right]
  congr 1
  ring



theorem oddPrismTransferBridgeRawMoment_neg_eq_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n (-r) =
      oddPrismTransferBridgeFlippedRawMoment beta n r := by
  unfold oddPrismTransferBridgeRawMoment
    oddPrismTransferBridgeFlippedRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive
      (V := Fin (2 * n + 1) × Fin (2 * n + 1))).toPerm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Function.Involutive.coe_toPerm]
  rw [oddPrismPureSeamKernel_flip_right]
  simp [isingSumConfigEquiv, Equiv.sumPiEquivProdPi]

theorem oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawFirst beta n (-r) =
      -oddPrismTransferBridgeFlippedRawFirst beta n r := by
  unfold oddPrismTransferBridgeRawFirst
    oddPrismTransferBridgeFlippedRawFirst
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive
      (V := Fin (2 * n + 1) × Fin (2 * n + 1))).toPerm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Function.Involutive.coe_toPerm]
  rw [oddPrismLayerSeamInteraction_flip_right,
    oddPrismPureSeamKernel_flip_right]
  simp only [neg_neg]
  ring

theorem oddPrismTransferBridgeRawSecond_neg_eq_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawSecond beta n (-r) =
      oddPrismTransferBridgeFlippedRawSecond beta n r := by
  unfold oddPrismTransferBridgeRawSecond
    oddPrismTransferBridgeFlippedRawSecond
  apply Finset.sum_congr rfl
  intro s _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive
      (V := Fin (2 * n + 1) × Fin (2 * n + 1))).toPerm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Function.Involutive.coe_toPerm]
  rw [oddPrismLayerSeamInteraction_flip_right,
    oddPrismPureSeamKernel_flip_right]
  simp only [neg_neg]
  ring


theorem oddPrismTransferBridgeVariance_neg_eq_flipped
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n (-r) =
      oddPrismTransferBridgeFlippedVariance beta n r := by
  unfold oddPrismTransferBridgeVariance
    oddPrismTransferBridgeFlippedVariance
  rw [oddPrismTransferBridgeRawMoment_neg_eq_flipped,
    oddPrismTransferBridgeRawFirst_neg_eq_neg_flipped,
    oddPrismTransferBridgeRawSecond_neg_eq_flipped]
  ring



noncomputable def oddPrismGraphBridgeRawMoment
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact ∑ a : ConfigSpace (OddPrismLowerBlockSite n),
    ∑ b : ConfigSpace (OddPrismUpperBlockSite n),
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        Real.exp (r * unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b)

noncomputable def oddPrismGraphBridgeRawFirst
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact ∑ a : ConfigSpace (OddPrismLowerBlockSite n),
    ∑ b : ConfigSpace (OddPrismUpperBlockSite n),
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        (unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b *
          Real.exp (r * unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b))

noncomputable def oddPrismGraphBridgeRawSecond
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact ∑ a : ConfigSpace (OddPrismLowerBlockSite n),
    ∑ b : ConfigSpace (OddPrismUpperBlockSite n),
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        (unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b ^ 2 *
          Real.exp (r * unequalReplicaBridgeInteraction
            (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
            (oddPrismUnequalGlueGraph n) a b))

theorem oddPrismGraphBridgeRawMoment_pos
    (beta : Real) (n : Nat) (r : Real) :
    0 < oddPrismGraphBridgeRawMoment beta n r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawMoment
  apply Finset.sum_pos
  · intro a _
    apply Finset.sum_pos
    · intro b _
      exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
        (Real.exp_pos _)
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty




theorem oddPrismUnequalBridgeVariance_eq_graphRaw
    (beta : Real) (n : Nat) (r : Real) :
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) r =
      oddPrismGraphBridgeRawSecond beta n r /
          oddPrismGraphBridgeRawMoment beta n r -
        (oddPrismGraphBridgeRawFirst beta n r /
          oddPrismGraphBridgeRawMoment beta n r) ^ 2 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold unequalReplicaBridgeVariance unequalReplicaBridgeMean
    unequalReplicaBridgeMoment oddPrismGraphBridgeRawMoment
    oddPrismGraphBridgeRawFirst oddPrismGraphBridgeRawSecond
  have hmul (a : ConfigSpace (OddPrismLowerBlockSite n))
      (b : ConfigSpace (OddPrismUpperBlockSite n)) :
      unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b * r =
        r * unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b := by ring
  field_simp [
    (ZJ_pos (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne',
    (ZJ_pos (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne']
  simp_rw [hmul]
  ring



theorem oddPrismGraphBridgeRawMoment_beta_eq_plusPartition
    (beta : Real) (n : Nat) :
    oddPrismGraphBridgeRawMoment beta n beta =
      rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  rw [rectangularPrismPlusPartition_eq_unequalBridge]
  unfold oddPrismUnequalBridgeMoment unequalReplicaBridgeMoment
    oddPrismGraphBridgeRawMoment
  field_simp [
    (ZJ_pos (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne',
    (ZJ_pos (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne']



theorem oddPrismTransferBridgeRawMoment_beta_eq_plusPartition
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismTransferBridgeRawMoment beta n beta =
      rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
  rw [oddPrismTransferBridgeRawMoment_eq_tailContraction,
    oddPrismTiltedSeamTransfer_eq_rectangularTransfer]
  rw [← oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]
  rw [rectangularPrismPlusPartition_eq_centerDenominator]
  apply Finset.sum_congr rfl
  intro s _
  simp only [oddPrismLowerTransferTail, pow_two]



theorem oddPrismGraphBridgeRawMoment_beta_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismGraphBridgeRawMoment beta n beta =
      oddPrismTransferBridgeRawMoment beta n beta := by
  rw [oddPrismGraphBridgeRawMoment_beta_eq_plusPartition,
    oddPrismTransferBridgeRawMoment_beta_eq_plusPartition beta n hn]





noncomputable def oddPrismBlockConfigEquiv (n : Nat) :
    (ConfigSpace (OddPrismLowerBlockSite n) ×
      ConfigSpace (OddPrismUpperBlockSite n)) ≃
        RectangularPrismConfig (2 * n + 1) (2 * n + 1) n :=
  isingSumConfigEquiv.symm |>.trans
    (isingCfgEquiv
      (StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n))).symm

@[simp] theorem spin_oddPrismBlockConfigEquiv_lower
    (n : Nat) (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n))
    (v : OddPrismLowerBlockSite n) :
    spin (oddPrismBlockConfigEquiv n (a, b)) v.1 = spin a v := by
  unfold spin
  congr 1
  unfold oddPrismBlockConfigEquiv
  simp only [Equiv.trans_apply, isingCfgEquiv, Equiv.coe_fn_symm_mk]
  rw [show (StatMech.FK.agl_sumEquiv
      (oddPrismAtOrBelowCenter n)).symm v.1 = Sum.inl v by
    exact Equiv.sumCompl_symm_apply_of_pos v.2]
  have h := isingSumConfigEquiv.apply_symm_apply (a, b)
  exact congrArg (fun x : Bool => x = true)
    (congrFun (congrArg Prod.fst h) v)

@[simp] theorem spin_oddPrismBlockConfigEquiv_upper
    (n : Nat) (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n))
    (v : OddPrismUpperBlockSite n) :
    spin (oddPrismBlockConfigEquiv n (a, b)) v.1 = spin b v := by
  unfold spin
  congr 1
  unfold oddPrismBlockConfigEquiv
  simp only [Equiv.trans_apply, isingCfgEquiv, Equiv.coe_fn_symm_mk]
  rw [show (StatMech.FK.agl_sumEquiv
      (oddPrismAtOrBelowCenter n)).symm v.1 = Sum.inr v by
    exact Equiv.sumCompl_symm_apply_of_neg v.2]
  have h := isingSumConfigEquiv.apply_symm_apply (a, b)
  exact congrArg (fun x : Bool => x = true)
    (congrFun (congrArg Prod.snd h) v)



noncomputable def oddPrismFullSeamInteraction (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  let p := (oddPrismBlockConfigEquiv n).symm sigma
  exact unequalReplicaBridgeInteraction
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) p.1 p.2



noncomputable def oddPrismFullTiltedRawMoment
    (beta : Real) (n : Nat) (r : Real) : Real :=
  ∑ sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n,
    wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) sigma *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma)

@[simp] theorem oddPrismFullSeamInteraction_join
    (n : Nat) (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n)) :
    oddPrismFullSeamInteraction n (oddPrismBlockConfigEquiv n (a, b)) =
      unequalReplicaBridgeInteraction
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) a b := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismFullSeamInteraction
  rw [Equiv.symm_apply_apply]



theorem oddPrismFullSeamInteraction_eq_rectangularInterface
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    oddPrismFullSeamInteraction n sigma =
      rectangularPrismInterfaceInteraction sigma := by
  let p := (oddPrismBlockConfigEquiv n).symm sigma
  have hsigma : oddPrismBlockConfigEquiv n p = sigma :=
    (oddPrismBlockConfigEquiv n).apply_symm_apply sigma
  rw [← hsigma]
  change oddPrismFullSeamInteraction n (oddPrismBlockConfigEquiv n p) = _
  rw [oddPrismFullSeamInteraction_join,
    oddPrismUnequalBridgeInteraction_eq_layerDotProduct n hn]
  unfold rectangularPrismInterfaceInteraction
  rw [dif_pos hn]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro y _
  rw [← spin_oddPrismLowerHalfSurfaceSite_eq_layer,
    ← spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer,
    ← spin_oddPrismBlockConfigEquiv_lower,
    ← spin_oddPrismBlockConfigEquiv_upper]
  rfl



theorem rectangularPrismInterfaceInteraction_eq_layerSeam
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismInterfaceInteraction sigma =
      oddPrismLayerSeamInteraction n
        (rectangularPrismLayer sigma ⟨n, by omega⟩)
        (rectangularPrismLayer sigma ⟨n + 1, by omega⟩) := by
  unfold rectangularPrismInterfaceInteraction oddPrismLayerSeamInteraction
    rectangularPrismLayer rectangularPrismSpin
  rw [dif_pos hn, Fintype.sum_prod_type]
  rfl



def oddPrismLayerPathSplitEquiv (E : Type*) (n : Nat) :
    (Fin (2 * n + 1) -> E) ≃
      ((Fin (n + 1) -> E) × (Fin n -> E)) where
  toFun q :=
    (fun k => q ⟨k.val, by omega⟩,
      fun k => q ⟨2 * n - k.val, by omega⟩)
  invFun p := fun z =>
    if hz : z.val <= n then p.1 ⟨z.val, by omega⟩
    else p.2 ⟨2 * n - z.val, by
      have hzLt := z.isLt
      omega⟩
  left_inv q := by
    funext z
    by_cases hz : z.val <= n
    · simp [hz]
    · simp [hz]
      congr
      have hzLt := z.isLt
      omega
  right_inv p := by
    apply Prod.ext
    · funext k
      have hk := k.isLt
      have hle : k.val <= n := by omega
      simp [hle]
    · funext k
      have hk := k.isLt
      have hnot : ¬2 * n - k.val <= n := by omega
      simp [hnot]
      apply congrArg p.2
      apply Fin.ext
      exact Nat.sub_sub_self (by omega)


def oddPrismSplitLayerPathConfigEquiv (n : Nat) :
    ((Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) ≃
        RectangularPrismConfig (2 * n + 1) (2 * n + 1) n :=
  (oddPrismLayerPathSplitEquiv
      (RectangularLayerConfig (2 * n + 1) (2 * n + 1)) n).symm.trans
    (rectangularPrismLayerEquiv (2 * n + 1) (2 * n + 1) n).symm

@[simp] theorem rectangularPrismLayer_splitConfig_lower
    (n : Nat)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin (n + 1)) :
    rectangularPrismLayer (oddPrismSplitLayerPathConfigEquiv n p)
        ⟨k.val, by omega⟩ = p.1 k := by
  unfold oddPrismSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply, rectangularPrismLayer_equiv_symm]
  have hk := k.isLt
  have hle : k.val <= n := by omega
  simp [oddPrismLayerPathSplitEquiv, hle]

@[simp] theorem rectangularPrismLayer_splitConfig_upper
    (n : Nat)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin n) :
    rectangularPrismLayer (oddPrismSplitLayerPathConfigEquiv n p)
        ⟨2 * n - k.val, by omega⟩ = p.2 k := by
  unfold oddPrismSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply, rectangularPrismLayer_equiv_symm]
  have hk := k.isLt
  have hnot : ¬2 * n - k.val <= n := by omega
  simp [oddPrismLayerPathSplitEquiv, hnot]
  apply congrArg p.2
  apply Fin.ext
  exact Nat.sub_sub_self (by omega)



def oddPrismPositiveSplitLayerPathConfigEquiv (n : Nat) (hn : 0 < n) :
    ((Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) ≃
        RectangularPrismConfig (2 * n + 1) (2 * n + 1) n :=
  (Equiv.prodCongr (Equiv.refl _)
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _))).trans
    (oddPrismSplitLayerPathConfigEquiv n)

@[simp] theorem rectangularPrismLayer_positiveSplitConfig_lower
    (n : Nat) (hn : 0 < n)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin (n + 1)) :
    rectangularPrismLayer (oddPrismPositiveSplitLayerPathConfigEquiv n hn p)
        ⟨k.val, by omega⟩ = p.1 k := by
  unfold oddPrismPositiveSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply, rectangularPrismLayer_splitConfig_lower]
  rfl

@[simp] theorem rectangularPrismLayer_positiveSplitConfig_upper
    (n : Nat) (hn : 0 < n)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1)))
    (k : Fin (n - 1 + 1)) :
    rectangularPrismLayer (oddPrismPositiveSplitLayerPathConfigEquiv n hn p)
        ⟨2 * n - k.val, by omega⟩ = p.2 k := by
  unfold oddPrismPositiveSplitLayerPathConfigEquiv
  rw [Equiv.trans_apply]
  have h := rectangularPrismLayer_splitConfig_upper n
    ((Equiv.prodCongr (Equiv.refl _)
      (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl _))) p)
    ((finCongr (by omega)) k)
  simpa using h



def oddPrismFullTiltedTransitionProduct (beta : Real) (n : Nat) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  ∏ z : Fin (2 * n), if z.val = n then
    B (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ)
  else
    A (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ)



theorem oddPrismFullTiltedTransitionProduct_positiveSplit
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
    oddPrismFullTiltedTransitionProduct beta n r
        (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) =
      (∏ j : Fin n, rectangularPrismTransfer 1 beta
          (2 * n + 1) (2 * n + 1) (p.1 j.castSucc) (p.1 j.succ)) *
        oddPrismTiltedSeamTransfer beta n r
          (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1))) *
        ∏ j : Fin (n - 1), rectangularPrismTransfer 1 beta
          (2 * n + 1) (2 * n + 1) (p.2 j.castSucc) (p.2 j.succ) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  let sigma := oddPrismPositiveSplitLayerPathConfigEquiv n hn p
  change (∏ z : Fin (2 * n), if z.val = n then
      B (rectangularPrismLayer sigma z.castSucc)
        (rectangularPrismLayer sigma z.succ)
    else A (rectangularPrismLayer sigma z.castSucc)
        (rectangularPrismLayer sigma z.succ)) = _
  let e : (Fin n ⊕ Fin n) ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← e.prod_comp, Fintype.prod_sum_type]
  have hleft : (∏ j : Fin n,
      if (e (Sum.inl j)).val = n then
        B (rectangularPrismLayer sigma (e (Sum.inl j)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inl j)).succ)
      else A (rectangularPrismLayer sigma (e (Sum.inl j)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inl j)).succ)) =
      ∏ j : Fin n, A (p.1 j.castSucc) (p.1 j.succ) := by
    apply Fintype.prod_congr
    intro j
    have hj := j.isLt
    have he : e (Sum.inl j) = ⟨j.val, by omega⟩ := by
      apply Fin.ext
      simp [e]
    have hne : (e (Sum.inl j)).val ≠ n := by
      rw [he]
      exact Nat.ne_of_lt hj
    rw [if_neg hne, he]
    congr 2
    · exact rectangularPrismLayer_positiveSplitConfig_lower n hn p j.castSucc
    · exact rectangularPrismLayer_positiveSplitConfig_lower n hn p j.succ
  rw [hleft]
  let c : Fin (n - 1 + 1) ≃ Fin n := finCongr (by omega)
  have hright : (∏ k : Fin n,
      if (e (Sum.inr k)).val = n then
        B (rectangularPrismLayer sigma (e (Sum.inr k)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inr k)).succ)
      else A (rectangularPrismLayer sigma (e (Sum.inr k)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inr k)).succ)) =
      B (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1))) *
        ∏ j : Fin (n - 1), A (p.2 j.castSucc) (p.2 j.succ) := by
    rw [← c.prod_comp, Fin.prod_univ_succ]
    congr 1
    · have hz : e (Sum.inr (c 0)) = ⟨n, by omega⟩ := by
        apply Fin.ext
        simp [e, c]
      rw [hz, if_pos rfl]
      congr 2
      · exact rectangularPrismLayer_positiveSplitConfig_lower n hn p
          (Fin.last n)
      · have hidx : (⟨n, by omega⟩ : Fin (2 * n)).succ =
            (⟨2 * n - (Fin.last (n - 1)).val, by omega⟩ :
              Fin (2 * n + 1)) := by
          apply Fin.ext
          simp
          omega
        rw [hidx]
        exact rectangularPrismLayer_positiveSplitConfig_upper n hn p
          (Fin.last (n - 1))
    · have hA : A.IsHermitian := rectangularPrismTransfer_isHermitian
          1 beta (2 * n + 1) (2 * n + 1)
      calc
        (∏ j : Fin (n - 1),
            if (e (Sum.inr (c j.succ))).val = n then
              B (rectangularPrismLayer sigma
                  (e (Sum.inr (c j.succ))).castSucc)
                (rectangularPrismLayer sigma (e (Sum.inr (c j.succ))).succ)
            else A (rectangularPrismLayer sigma
                  (e (Sum.inr (c j.succ))).castSucc)
                (rectangularPrismLayer sigma (e (Sum.inr (c j.succ))).succ)) =
            ∏ j : Fin (n - 1), A (p.2 (Fin.revPerm j).castSucc)
              (p.2 (Fin.revPerm j).succ) := by
          apply Fintype.prod_congr
          intro j
          let k := Fin.revPerm j
          have hz : e (Sum.inr (c j.succ)) =
              ⟨n + 1 + j.val, by omega⟩ := by
            apply Fin.ext
            simp [e, c]
            omega
          have hne : (e (Sum.inr (c j.succ))).val ≠ n := by
            rw [hz]
            change n + 1 + j.val ≠ n
            omega
          rw [if_neg hne, hz]
          have hidx1 :
              (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).castSucc =
                (⟨2 * n - (k.succ).val, by omega⟩ : Fin (2 * n + 1)) := by
            apply Fin.ext
            simp [k, Fin.revPerm_apply]
            omega
          have hq1 : rectangularPrismLayer sigma
                (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).castSucc =
              p.2 k.succ := by
            rw [hidx1]
            exact rectangularPrismLayer_positiveSplitConfig_upper n hn p k.succ
          have hidx2 : (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).succ =
              (⟨2 * n - (k.castSucc).val, by omega⟩ : Fin (2 * n + 1)) := by
            apply Fin.ext
            simp [k, Fin.revPerm_apply]
            omega
          have hq2 : rectangularPrismLayer sigma
                (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).succ =
              p.2 k.castSucc := by
            rw [hidx2]
            exact rectangularPrismLayer_positiveSplitConfig_upper n hn p k.castSucc
          rw [hq1, hq2]
          have hs := hA.apply (p.2 k.castSucc) (p.2 k.succ)
          simpa only [star_trivial] using hs
        _ = ∏ j : Fin (n - 1), A (p.2 j.castSucc) (p.2 j.succ) := by
          apply Fintype.prod_equiv Fin.revPerm
          intro j
          rfl
  rw [hright]
  ring



theorem oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    oddPrismFullTiltedTransitionProduct beta n r sigma =
      (∏ z : Fin (2 * n), rectangularPrismTransfer 1 beta
        (2 * n + 1) (2 * n + 1)
        (rectangularPrismLayer sigma z.castSucc)
        (rectangularPrismLayer sigma z.succ)) *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  let z0 : Fin (2 * n) := ⟨n, by omega⟩
  let f : Fin (2 * n) -> Real := fun z =>
    A (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ)
  let g : Fin (2 * n) -> Real := fun z => if z.val = n then
    B (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ) else f z
  change (∏ z, g z) = (∏ z, f z) * _
  have hI : oddPrismFullSeamInteraction n sigma =
      oddPrismLayerSeamInteraction n
        (rectangularPrismLayer sigma z0.castSucc)
        (rectangularPrismLayer sigma z0.succ) := by
    rw [oddPrismFullSeamInteraction_eq_rectangularInterface n hn sigma,
      rectangularPrismInterfaceInteraction_eq_layerSeam n hn sigma]
    congr 1
  rw [hI]
  have hz0 : z0 ∈ (Finset.univ : Finset (Fin (2 * n))) := Finset.mem_univ _
  have hgErase : (∏ z ∈ (Finset.univ.erase z0), g z) =
      ∏ z ∈ (Finset.univ.erase z0), f z := by
    apply Finset.prod_congr rfl
    intro z hz
    have hne : z ≠ z0 := (Finset.mem_erase.mp hz).1
    have hval : z.val ≠ n := by
      intro hv
      apply hne
      apply Fin.ext
      exact hv
    simp [g, hval]
  calc
    (∏ z, g z) = g z0 * ∏ z ∈ (Finset.univ.erase z0), g z := by
      exact (Finset.mul_prod_erase Finset.univ g hz0).symm
    _ = B (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ) *
        ∏ z ∈ (Finset.univ.erase z0), f z := by
      rw [hgErase]
      congr 1
      simp [g, z0]
    _ = (A (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ) *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n
          (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ))) *
        ∏ z ∈ (Finset.univ.erase z0), f z := by
      dsimp only [B, A]
      rw [oddPrismTiltedSeamTransfer_eq_transfer_mul_exp]
    _ = (A (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ) *
        ∏ z ∈ (Finset.univ.erase z0), f z) *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n
          (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ)) := by ring
    _ = (∏ z, f z) *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n
          (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ)) := by
      rw [Finset.mul_prod_erase Finset.univ f hz0]



def oddPrismFullTiltedPathWeight (beta : Real) (n : Nat) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  a (rectangularPrismLayer sigma 0) *
    oddPrismFullTiltedTransitionProduct beta n r sigma *
    a (rectangularPrismLayer sigma (Fin.last (2 * n)))



theorem oddPrismFullTiltedWeight_eq_pathWeight
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) sigma *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma) =
        oddPrismFullTiltedPathWeight beta n r sigma := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  let q := rectangularPrismLayer sigma
  have hw : wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) sigma =
      Real.exp (-beta * rectangularPrismPlusEnergy 1 sigma) := by
    rw [oddPrismInternalGraph_edgeFinset]
    calc
      wJ (oddPrismInternalEdges n) (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v) sigma =
        Real.exp (beta * inhomogeneousInteraction (oddPrismInternalEdges n)
          (fun _ => 1) (oddPrismPlusField n) sigma) := by
            simpa using scaled_wJ_eq_exp_interaction (oddPrismInternalEdges n)
              (fun _ => 1) (oddPrismPlusField n) sigma beta
      _ = _ := by
        rw [oddPrism_plus_inhomogeneousInteraction]
        congr 1
        ring
  have hpath := rectangularPrismTransferPathWeight_eq_exp 1 beta
    (2 * n + 1) (2 * n + 1) n q
  have hexp := rectangularPrismPlusExponent_eq_layers 1 beta sigma
  have hord : a (q 0) *
        (∏ z : Fin (2 * n), A (q z.castSucc) (q z.succ)) *
        a (q (Fin.last (2 * n))) =
      Real.exp (-beta * rectangularPrismPlusEnergy 1 sigma) := by
    exact hpath.trans (congrArg Real.exp hexp.symm)
  unfold oddPrismFullTiltedPathWeight
  rw [oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp
    beta n hn r sigma]
  rw [hw, ← hord]
  ring


def transferTailPathWeight {E : Type*} [Fintype E]
    (A : Matrix E E Real) (a : E -> Real) (k : Nat)
    (q : Fin (k + 1) -> E) : Real :=
  a (q 0) * ∏ j : Fin k, A (q j.castSucc) (q j.succ)



theorem sum_transferTailPathWeight_mul_endpoint
    {E : Type*} [Fintype E] [DecidableEq E]
    (A : Matrix E E Real) (hA : A.IsHermitian)
    (a f : E -> Real) (k : Nat) :
    (∑ q : Fin (k + 1) -> E,
      transferTailPathWeight A a k q * f (q (Fin.last k))) =
      ∑ s, ((A ^ k) *ᵥ a) s * f s := by
  have hpath := dot_mulVec_pow_eq_sum_path A a f k
  unfold transferTailPathWeight
  rw [← hpath]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [show (∑ x, a x * ((A ^ k) x s * f s)) =
      (∑ x, (A ^ k) s x * a x) * f s by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    have hs := (hA.pow k).apply s x
    simp only [star_trivial] at hs
    rw [hs]
    ring]


def oddPrismSplitPathWeight (beta : Real) (n : Nat)
    (r : Real)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) : Real :=
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  transferTailPathWeight A a n p.1 *
    transferTailPathWeight A a (n - 1) p.2 *
    oddPrismTiltedSeamTransfer beta n r
      (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1)))



theorem oddPrismFullTiltedPathWeight_positiveSplit
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
    oddPrismFullTiltedPathWeight beta n r
        (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) =
      oddPrismSplitPathWeight beta n r p := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  let sigma := oddPrismPositiveSplitLayerPathConfigEquiv n hn p
  change a (rectangularPrismLayer sigma 0) *
      oddPrismFullTiltedTransitionProduct beta n r sigma *
      a (rectangularPrismLayer sigma (Fin.last (2 * n))) =
    (a (p.1 0) * ∏ j : Fin n, A (p.1 j.castSucc) (p.1 j.succ)) *
      (a (p.2 0) *
        ∏ j : Fin (n - 1), A (p.2 j.castSucc) (p.2 j.succ)) *
      B (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1)))
  rw [oddPrismFullTiltedTransitionProduct_positiveSplit beta n hn r p]
  have hzero : rectangularPrismLayer sigma 0 = p.1 0 := by
    exact rectangularPrismLayer_positiveSplitConfig_lower n hn p 0
  have hlast : rectangularPrismLayer sigma (Fin.last (2 * n)) = p.2 0 := by
    convert rectangularPrismLayer_positiveSplitConfig_upper n hn p 0 using 1
  rw [hzero, hlast]
  ring

set_option maxHeartbeats 800000 in

theorem sum_oddPrismSplitPathWeight_eq_transferRawMoment
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ p, oddPrismSplitPathWeight beta n r p) =
      oddPrismTransferBridgeRawMoment beta n r := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  have hA : A.IsHermitian :=
    rectangularPrismTransfer_isHermitian 1 beta (2 * n + 1) (2 * n + 1)
  rw [oddPrismTransferBridgeRawMoment_eq_tailContraction]
  change (∑ p : (Fin (n + 1) -> _) × (Fin (n - 1 + 1) -> _),
      transferTailPathWeight A a n p.1 *
      transferTailPathWeight A a (n - 1) p.2 *
        B (p.1 (Fin.last n))
          (p.2 (Fin.last (n - 1)))) =
    ∑ s, ((A ^ n) *ᵥ a) s * (B *ᵥ ((A ^ (n - 1)) *ᵥ a)) s
  rw [Fintype.sum_prod_type]
  calc
    (∑ lower, ∑ upper,
        transferTailPathWeight A a n lower *
          transferTailPathWeight A a (n - 1) upper *
            B (lower (Fin.last n)) (upper (Fin.last (n - 1)))) =
        ∑ lower, transferTailPathWeight A a n lower *
          (∑ t, ((A ^ (n - 1)) *ᵥ a) t *
            B (lower (Fin.last n)) t) := by
      apply Finset.sum_congr rfl
      intro lower _
      calc
        (∑ upper, transferTailPathWeight A a n lower *
            transferTailPathWeight A a (n - 1) upper *
              B (lower (Fin.last n)) (upper (Fin.last (n - 1)))) =
            transferTailPathWeight A a n lower *
              (∑ upper, transferTailPathWeight A a (n - 1) upper *
                B (lower (Fin.last n)) (upper (Fin.last (n - 1)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro upper _
          ring
        _ = transferTailPathWeight A a n lower *
              (∑ t, ((A ^ (n - 1)) *ᵥ a) t *
                B (lower (Fin.last n)) t) := by
          congr 1
          exact sum_transferTailPathWeight_mul_endpoint A hA a
            (fun t => B (lower (Fin.last n)) t) (n - 1)
    _ = ∑ s, ((A ^ n) *ᵥ a) s *
        (∑ t, ((A ^ (n - 1)) *ᵥ a) t * B s t) := by
      exact sum_transferTailPathWeight_mul_endpoint A hA a
        (fun s => ∑ t, ((A ^ (n - 1)) *ᵥ a) t * B s t) n
    _ = ∑ s, ((A ^ n) *ᵥ a) s *
        (B *ᵥ ((A ^ (n - 1)) *ᵥ a)) s := by
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro t _
      ring



theorem oddPrismFullTiltedRawMoment_eq_transferRawMoment
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismFullTiltedRawMoment beta n r =
      oddPrismTransferBridgeRawMoment beta n r := by
  unfold oddPrismFullTiltedRawMoment
  rw [← Equiv.sum_comp (oddPrismPositiveSplitLayerPathConfigEquiv n hn)]
  simp_rw [oddPrismFullTiltedWeight_eq_pathWeight beta n hn r]
  simp_rw [oddPrismFullTiltedPathWeight_positiveSplit beta n hn r]
  exact sum_oddPrismSplitPathWeight_eq_transferRawMoment beta n hn r

theorem oddPrismFullTiltedWeight_factor
    (beta : Real) (n : Nat) (r : Real)
    (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n)) :
    wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v)
        (oddPrismBlockConfigEquiv n (a, b)) *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n
        (oddPrismBlockConfigEquiv n (a, b))) =
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        Real.exp (r * unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b) := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  let e := StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n)
  let sigma := oddPrismBlockConfigEquiv n (a, b)
  have hcfg : isingCfgEquiv e sigma = isingSumConfigEquiv.symm (a, b) := by
    dsimp [sigma, oddPrismBlockConfigEquiv, e]
    rw [Equiv.apply_symm_apply]
  have hrel := ghsi_wJ_const_relabel
    (oddPrismUnequalGlueGraph n) (oddPrismInternalGraph n) e
    (by
      intro u v
      simpa [oddPrismUnequalGlueGraph, e] using
        (StatMech.FK.agl_glueGraph_adj
          (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n) u v))
    beta
    (Sum.elim
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))
    (fun v => beta * oddPrismPlusField n v) (by
      intro v
      rcases v with v | v <;> rfl) sigma
  rw [hcfg] at hrel
  have hfactor := wJ_crossInterface_factor
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n)
    (StatMech.FK.agl_partitionCrossInterface
      (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n)) beta
    (fun v : OddPrismLowerBlockSite n =>
      beta * oddPrismPlusField n v.1)
    (fun v : OddPrismUpperBlockSite n =>
      beta * oddPrismPlusField n v.1) a b
  have hrelmul := congrArg (fun z => z *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n
        (oddPrismBlockConfigEquiv n (a, b)))) hrel.symm
  calc
    _ = wJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta)
          (Sum.elim
            (fun v : OddPrismLowerBlockSite n =>
              beta * oddPrismPlusField n v.1)
            (fun v : OddPrismUpperBlockSite n =>
              beta * oddPrismPlusField n v.1))
          (isingSumConfigEquiv.symm (a, b)) *
        Real.exp ((r - beta) * oddPrismFullSeamInteraction n
          (oddPrismBlockConfigEquiv n (a, b))) := by
        convert hrelmul using 1
        dsimp only [sigma]
        unfold wJ
        apply congrArg (fun z : Real => z *
          Real.exp ((r - beta) * oddPrismFullSeamInteraction n
            (oddPrismBlockConfigEquiv n (a, b))))
        apply congrArg Real.exp
        apply congrArg (fun z : Real => z +
          ∑ x, (beta * oddPrismPlusField n x) *
            spin (oddPrismBlockConfigEquiv n (a, b)) x)
        apply Finset.sum_congr
        · ext edge
          simp only [SimpleGraph.mem_edgeFinset]
        · intro edge _
          rfl
    _ = _ := by
      rw [hfactor, oddPrismFullSeamInteraction_join]
      let I := unequalReplicaBridgeInteraction
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) a b
      let WL := wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1) a
      let WU := wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1) b
      change WL * WU * Real.exp (beta * I) *
          Real.exp ((r - beta) * I) = WL * WU * Real.exp (r * I)
      rw [show WL * WU * Real.exp (beta * I) *
          Real.exp ((r - beta) * I) =
        WL * WU * (Real.exp (beta * I) *
          Real.exp ((r - beta) * I)) by ring,
        ← Real.exp_add]
      congr 2
      ring



theorem oddPrismGraphBridgeRawMoment_eq_fullTilted
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismGraphBridgeRawMoment beta n r =
      oddPrismFullTiltedRawMoment beta n r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawMoment oddPrismFullTiltedRawMoment
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (oddPrismBlockConfigEquiv n)]
  apply Finset.sum_congr rfl
  intro p _
  exact (oddPrismFullTiltedWeight_factor beta n r p.1 p.2).symm



theorem oddPrismGraphBridgeRawMoment_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismGraphBridgeRawMoment beta n r =
      oddPrismTransferBridgeRawMoment beta n r := by
  rw [oddPrismGraphBridgeRawMoment_eq_fullTilted,
    oddPrismFullTiltedRawMoment_eq_transferRawMoment beta n hn r]



theorem hasDerivAt_weightedSeamExp (w I r : Real) :
    HasDerivAt (fun t => w * Real.exp (t * I))
      (w * (I * Real.exp (r * I))) r := by
  have hi : HasDerivAt (fun t : Real => t * I) I r := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id r).mul_const I
  convert ((Real.hasDerivAt_exp (r * I)).comp r hi).const_mul w using 1 <;> ring

theorem hasDerivAt_weightedSeamFirst (w I r : Real) :
    HasDerivAt (fun t => w * (I * Real.exp (t * I)))
      (w * (I ^ 2 * Real.exp (r * I))) r := by
  convert hasDerivAt_weightedSeamExp (w * I) I r using 1 <;> ring

theorem hasDerivAt_oddPrismTransferBridgeRawMoment
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismTransferBridgeRawMoment beta n)
      (oddPrismTransferBridgeRawFirst beta n r) r := by
  unfold oddPrismTransferBridgeRawMoment oddPrismTransferBridgeRawFirst
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun s _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun q _ =>
      hasDerivAt_weightedSeamExp
        (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n q)
        (oddPrismLayerSeamInteraction n s q) r))
  convert h using 1
  funext t
  simp only [oddPrismPureSeamKernel, Finset.sum_apply]

theorem hasDerivAt_oddPrismTransferBridgeRawFirst
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismTransferBridgeRawFirst beta n)
      (oddPrismTransferBridgeRawSecond beta n r) r := by
  unfold oddPrismTransferBridgeRawFirst oddPrismTransferBridgeRawSecond
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun s _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun q _ =>
      hasDerivAt_weightedSeamFirst
        (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n q)
        (oddPrismLayerSeamInteraction n s q) r))
  convert h using 1
  funext t
  simp only [oddPrismPureSeamKernel, Finset.sum_apply]

theorem hasDerivAt_oddPrismGraphBridgeRawMoment
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismGraphBridgeRawMoment beta n)
      (oddPrismGraphBridgeRawFirst beta n r) r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawMoment oddPrismGraphBridgeRawFirst
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun a _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun b _ =>
      hasDerivAt_weightedSeamExp
        (wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) a *
          wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) b)
        (unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b) r))
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

theorem hasDerivAt_oddPrismGraphBridgeRawFirst
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismGraphBridgeRawFirst beta n)
      (oddPrismGraphBridgeRawSecond beta n r) r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawFirst oddPrismGraphBridgeRawSecond
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun a _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun b _ =>
      hasDerivAt_weightedSeamFirst
        (wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) a *
          wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) b)
        (unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b) r))
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

theorem oddPrismGraphBridgeRawFirst_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismGraphBridgeRawFirst beta n r =
      oddPrismTransferBridgeRawFirst beta n r := by
  have hfun : oddPrismGraphBridgeRawMoment beta n =
      oddPrismTransferBridgeRawMoment beta n := by
    funext t
    exact oddPrismGraphBridgeRawMoment_eq_transfer beta n hn t
  have hd := congrArg (fun f : Real -> Real => deriv f r) hfun
  change deriv (oddPrismGraphBridgeRawMoment beta n) r =
    deriv (oddPrismTransferBridgeRawMoment beta n) r at hd
  rw [(hasDerivAt_oddPrismGraphBridgeRawMoment beta n r).deriv,
    (hasDerivAt_oddPrismTransferBridgeRawMoment beta n r).deriv] at hd
  exact hd

theorem oddPrismGraphBridgeRawSecond_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismGraphBridgeRawSecond beta n r =
      oddPrismTransferBridgeRawSecond beta n r := by
  have hfun : oddPrismGraphBridgeRawFirst beta n =
      oddPrismTransferBridgeRawFirst beta n := by
    funext t
    exact oddPrismGraphBridgeRawFirst_eq_transfer beta n hn t
  have hd := congrArg (fun f : Real -> Real => deriv f r) hfun
  change deriv (oddPrismGraphBridgeRawFirst beta n) r =
    deriv (oddPrismTransferBridgeRawFirst beta n) r at hd
  rw [(hasDerivAt_oddPrismGraphBridgeRawFirst beta n r).deriv,
    (hasDerivAt_oddPrismTransferBridgeRawFirst beta n r).deriv] at hd
  exact hd


theorem oddPrismUnequalBridgeVariance_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) r =
      oddPrismTransferBridgeVariance beta n r := by
  rw [oddPrismUnequalBridgeVariance_eq_graphRaw,
    oddPrismGraphBridgeRawMoment_eq_transfer beta n hn r,
    oddPrismGraphBridgeRawFirst_eq_transfer beta n hn r,
    oddPrismGraphBridgeRawSecond_eq_transfer beta n hn r]
  rfl



def oddPrismTransferBridgeVarianceNumerator
    (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeRawSecond beta n r *
      oddPrismTransferBridgeRawMoment beta n r -
    oddPrismTransferBridgeRawFirst beta n r ^ 2

def oddPrismTransferBridgeVarianceSkewNumerator
    (beta : Real) (n : Nat) (r : Real) : Real :=
  oddPrismTransferBridgeVarianceNumerator beta n r *
      oddPrismTransferBridgeRawMoment beta n (-r) ^ 2 -
    oddPrismTransferBridgeVarianceNumerator beta n (-r) *
      oddPrismTransferBridgeRawMoment beta n r ^ 2

theorem oddPrismTransferBridgeRawMoment_pos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 < oddPrismTransferBridgeRawMoment beta n r := by
  rw [← oddPrismGraphBridgeRawMoment_eq_transfer beta n hn r]
  exact oddPrismGraphBridgeRawMoment_pos beta n r



theorem oddPrismTransferBridgeVariance_eq_numerator_div
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      oddPrismTransferBridgeVarianceNumerator beta n r /
        oddPrismTransferBridgeRawMoment beta n r ^ 2 := by
  have hp := (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'
  unfold oddPrismTransferBridgeVariance
    oddPrismTransferBridgeVarianceNumerator
  field_simp



theorem hasDerivAt_oddPrismTransferBridgeLogRawMoment
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    HasDerivAt
      (fun t => Real.log (oddPrismTransferBridgeRawMoment beta n t))
      (oddPrismTransferBridgeRawFirst beta n r /
        oddPrismTransferBridgeRawMoment beta n r) r := by
  exact (hasDerivAt_oddPrismTransferBridgeRawMoment beta n r).log
    (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'

theorem hasDerivAt_oddPrismTransferBridgeLogDerivative
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    HasDerivAt
      (fun t => oddPrismTransferBridgeRawFirst beta n t /
        oddPrismTransferBridgeRawMoment beta n t)
      (oddPrismTransferBridgeVariance beta n r) r := by
  have h := (hasDerivAt_oddPrismTransferBridgeRawFirst beta n r).div
    (hasDerivAt_oddPrismTransferBridgeRawMoment beta n r)
    (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'
  convert h using 1
  unfold oddPrismTransferBridgeVariance
  field_simp



theorem oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeVariance beta n r <=
        oddPrismTransferBridgeVariance beta n (-r) ↔
      oddPrismTransferBridgeVarianceSkewNumerator beta n r <= 0 := by
  rw [oddPrismTransferBridgeVariance_eq_numerator_div beta n hn r,
    oddPrismTransferBridgeVariance_eq_numerator_div beta n hn (-r)]
  have hp := oddPrismTransferBridgeRawMoment_pos beta n hn r
  have hm := oddPrismTransferBridgeRawMoment_pos beta n hn (-r)
  rw [div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos hm)]
  unfold oddPrismTransferBridgeVarianceSkewNumerator
  constructor <;> intro h <;> linarith



def finiteExpMoment {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  ∑ x, w x * Real.exp (r * I x)

def finiteExpFirst {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  ∑ x, w x * (I x * Real.exp (r * I x))

def finiteExpSecond {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  ∑ x, w x * (I x ^ 2 * Real.exp (r * I x))

def finiteExpVarianceSkew {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  (finiteExpSecond w I r * finiteExpMoment w I r -
      finiteExpFirst w I r ^ 2) * finiteExpMoment w I (-r) ^ 2 -
    (finiteExpSecond w I (-r) * finiteExpMoment w I (-r) -
      finiteExpFirst w I (-r) ^ 2) * finiteExpMoment w I r ^ 2


theorem two_mul_finiteExpVarianceNumerator_eq_pairSum
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real) :
    2 * (finiteExpSecond w I r * finiteExpMoment w I r -
      finiteExpFirst w I r ^ 2) =
      ∑ x, ∑ y, w x * w y *
        ((I x - I y) ^ 2 * Real.exp (r * (I x + I y))) := by
  rw [show 2 * (finiteExpSecond w I r * finiteExpMoment w I r -
        finiteExpFirst w I r ^ 2) =
      finiteExpSecond w I r * finiteExpMoment w I r +
        finiteExpMoment w I r * finiteExpSecond w I r -
        2 * (finiteExpFirst w I r * finiteExpFirst w I r) by ring]
  unfold finiteExpMoment finiteExpFirst finiteExpSecond
  have hexp (x y : E) : Real.exp (r * (I x + I y)) =
      Real.exp (r * I x) * Real.exp (r * I y) := by
    rw [show r * (I x + I y) = r * I x + r * I y by ring,
      Real.exp_add]
  simp_rw [hexp]
  simp only [pow_two]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring




theorem two_mul_finiteExpVarianceSkew_eq_fourStateSum
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real) :
    2 * finiteExpVarianceSkew w I r =
      ∑ x, ∑ y, ∑ z, ∑ q,
        w x * w y * w z * w q * (I x - I y) ^ 2 *
          (Real.exp (r * (I x + I y - I z - I q)) -
            Real.exp (-r * (I x + I y - I z - I q))) := by
  unfold finiteExpVarianceSkew
  rw [show 2 *
      ((finiteExpSecond w I r * finiteExpMoment w I r -
          finiteExpFirst w I r ^ 2) * finiteExpMoment w I (-r) ^ 2 -
        (finiteExpSecond w I (-r) * finiteExpMoment w I (-r) -
          finiteExpFirst w I (-r) ^ 2) * finiteExpMoment w I r ^ 2) =
      (2 * (finiteExpSecond w I r * finiteExpMoment w I r -
          finiteExpFirst w I r ^ 2)) * finiteExpMoment w I (-r) ^ 2 -
        (2 * (finiteExpSecond w I (-r) * finiteExpMoment w I (-r) -
          finiteExpFirst w I (-r) ^ 2)) * finiteExpMoment w I r ^ 2 by ring]
  rw [two_mul_finiteExpVarianceNumerator_eq_pairSum,
    two_mul_finiteExpVarianceNumerator_eq_pairSum]
  unfold finiteExpMoment
  simp only [pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hp (x y z q : E) : Real.exp (r * (I x + I y)) *
      (Real.exp (-r * I z) * Real.exp (-r * I q)) =
      Real.exp (r * (I x + I y - I z - I q)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hm (x y z q : E) : Real.exp (-r * (I x + I y)) *
      (Real.exp (r * I z) * Real.exp (r * I q)) =
      Real.exp (-r * (I x + I y - I z - I q)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro q _
  calc
    w x * w y * ((I x - I y) * (I x - I y) *
          Real.exp (r * (I x + I y))) *
          (w z * Real.exp (-r * I z) * (w q * Real.exp (-r * I q))) -
        w x * w y * ((I x - I y) * (I x - I y) *
          Real.exp (-r * (I x + I y))) *
          (w z * Real.exp (r * I z) * (w q * Real.exp (r * I q))) =
      w x * w y * w z * w q * ((I x - I y) * (I x - I y)) *
        (Real.exp (r * (I x + I y)) *
            (Real.exp (-r * I z) * Real.exp (-r * I q)) -
          Real.exp (-r * (I x + I y)) *
            (Real.exp (r * I z) * Real.exp (r * I q))) := by ring
    _ = _ := by rw [hp, hm]

def oddPrismTransferPairBaseWeight (beta : Real) (n : Nat) :
    (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real :=
  fun x => oddPrismLowerConditionedVector beta n x.1 *
    oddPrismUpperConditionedVector beta n x.2

def oddPrismTransferPairInteraction (n : Nat) :
    (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real :=
  fun x => oddPrismLayerSeamInteraction n x.1 x.2



theorem oddPrismLowerConditionedVector_eq_threeLayerEndpoint
    (beta : Real) (n : Nat) (hn : 0 < n)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLowerConditionedVector beta n s =
      oddPrismLayerHalfWeight beta n s ^ 2 *
        ∑ v, oddPrismPureSeamKernel beta n s v *
          oddPrismUpperConditionedVector beta n v := by
  unfold oddPrismLowerConditionedVector
  rw [oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]
  rw [← oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n]
  unfold Matrix.mulVec dotProduct oddPrismTiltedSeamTransfer
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  unfold oddPrismUpperConditionedVector
  ring



def oddPrismThreeLayerRawMoment
    (beta : Real) (n : Nat) (a b : Real) : Real :=
  ∑ s, ∑ v, ∑ t,
    oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperConditionedVector beta n v *
      oddPrismUpperConditionedVector beta n t *
      oddPrismPureSeamKernel a n s v *
      oddPrismPureSeamKernel b n s t

def oddPrismThreeLayerWeight
    (beta : Real) (n : Nat) (a b : Real)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  oddPrismLayerHalfWeight beta n s ^ 2 *
    oddPrismUpperConditionedVector beta n v *
    oddPrismUpperConditionedVector beta n t *
    oddPrismPureSeamKernel a n s v *
    oddPrismPureSeamKernel b n s t




theorem oddPrismThreeLayerWeight_swap
    (beta : Real) (n : Nat) (a b : Real)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismThreeLayerWeight beta n a b s t v =
      oddPrismThreeLayerWeight beta n a b s v t *
        Real.exp ((a - b) *
          (oddPrismLayerSeamInteraction n s t -
            oddPrismLayerSeamInteraction n s v)) := by
  let C := oddPrismLayerHalfWeight beta n s ^ 2 *
    oddPrismUpperConditionedVector beta n v *
    oddPrismUpperConditionedVector beta n t
  rw [show oddPrismThreeLayerWeight beta n a b s t v = C *
      (Real.exp (a * oddPrismLayerSeamInteraction n s t) *
        Real.exp (b * oddPrismLayerSeamInteraction n s v)) by
    unfold oddPrismThreeLayerWeight oddPrismPureSeamKernel C
    ring]
  rw [show oddPrismThreeLayerWeight beta n a b s v t *
      Real.exp ((a - b) *
        (oddPrismLayerSeamInteraction n s t -
          oddPrismLayerSeamInteraction n s v)) = C *
      (Real.exp (a * oddPrismLayerSeamInteraction n s v) *
        Real.exp (b * oddPrismLayerSeamInteraction n s t) *
        Real.exp ((a - b) *
          (oddPrismLayerSeamInteraction n s t -
            oddPrismLayerSeamInteraction n s v))) by
    unfold oddPrismThreeLayerWeight oddPrismPureSeamKernel C
    ring]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem rectangularPrismTransfer_pow_mulVec_boundary_pos
    (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < ((rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) ^ k) *ᵥ
      rectangularPrismTransferBoundaryVector
        1 beta (2 * n + 1) (2 * n + 1)) s := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  change 0 < ((A ^ k) *ᵥ a) s
  induction k generalizing s with
  | zero =>
      simp only [pow_zero, one_mulVec]
      exact rectangularPrismTransferBoundaryVector_pos
        1 beta (2 * n + 1) (2 * n + 1) s
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_pos
      · intro t _
        exact mul_pos
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) s t) (ih t)
      · exact Finset.univ_nonempty

theorem oddPrismUpperConditionedVector_pos
    (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismUpperConditionedVector beta n s := by
  unfold oddPrismUpperConditionedVector oddPrismUpperTransferTail
  exact mul_pos (oddPrismLayerHalfWeight_pos beta n s)
    (rectangularPrismTransfer_pow_mulVec_boundary_pos beta n (n - 1) s)

theorem oddPrismThreeLayerWeight_pos
    (beta : Real) (n : Nat) (a b : Real)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismThreeLayerWeight beta n a b s v t := by
  unfold oddPrismThreeLayerWeight
  exact mul_pos (mul_pos (mul_pos (mul_pos
    (sq_pos_of_pos (oddPrismLayerHalfWeight_pos beta n s))
    (oddPrismUpperConditionedVector_pos beta n v))
    (oddPrismUpperConditionedVector_pos beta n t))
    (oddPrismPureSeamKernel_pos a n s v))
    (oddPrismPureSeamKernel_pos b n s t)



theorem oddPrismThreeLayerWeight_le_swap
    (beta : Real) (n : Nat) {a b : Real} (hba : b <= a)
    (s v t : RectangularLayerConfig (2 * n + 1) (2 * n + 1))
    (hI : oddPrismLayerSeamInteraction n s v <=
      oddPrismLayerSeamInteraction n s t) :
    oddPrismThreeLayerWeight beta n a b s v t <=
      oddPrismThreeLayerWeight beta n a b s t v := by
  have hswap := oddPrismThreeLayerWeight_swap beta n a b s v t
  rw [hswap]
  apply le_mul_of_one_le_right
    (oddPrismThreeLayerWeight_pos beta n a b s v t).le
  apply Real.one_le_exp
  exact mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hI)

theorem oddPrismTransferBridgeRawMoment_eq_threeLayer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      oddPrismThreeLayerRawMoment beta n beta r := by
  unfold oddPrismTransferBridgeRawMoment oddPrismThreeLayerRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s]
  calc
    (∑ t, (oddPrismLayerHalfWeight beta n s ^ 2 *
        ∑ v, oddPrismPureSeamKernel beta n s v *
          oddPrismUpperConditionedVector beta n v) *
        oddPrismUpperConditionedVector beta n t *
        oddPrismPureSeamKernel r n s t) =
      ∑ t, ∑ v, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismUpperConditionedVector beta n v *
        oddPrismUpperConditionedVector beta n t *
        oddPrismPureSeamKernel beta n s v *
        oddPrismPureSeamKernel r n s t := by
          apply Finset.sum_congr rfl
          intro t _
          rw [show (oddPrismLayerHalfWeight beta n s ^ 2 *
              ∑ v, oddPrismPureSeamKernel beta n s v *
                oddPrismUpperConditionedVector beta n v) *
              oddPrismUpperConditionedVector beta n t *
              oddPrismPureSeamKernel r n s t =
            (∑ v, oddPrismPureSeamKernel beta n s v *
                oddPrismUpperConditionedVector beta n v) *
              (oddPrismLayerHalfWeight beta n s ^ 2 *
                oddPrismUpperConditionedVector beta n t *
                oddPrismPureSeamKernel r n s t) by ring]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _
          ring
    _ = _ := by rw [Finset.sum_comm]




theorem oddPrismThreeLayerRawMoment_symm
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b =
      oddPrismThreeLayerRawMoment beta n b a := by
  unfold oddPrismThreeLayerRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  ring



def oddPrismThreeLayerMarkedRawMoment
    (beta : Real) (n : Nat) (a b : Real) (F : Real -> Real -> Real) : Real :=
  ∑ s, ∑ v, ∑ t,
    oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperConditionedVector beta n v *
      oddPrismUpperConditionedVector beta n t *
      oddPrismPureSeamKernel a n s v *
      oddPrismPureSeamKernel b n s t *
      F (oddPrismLayerSeamInteraction n s v)
        (oddPrismLayerSeamInteraction n s t)

theorem oddPrismThreeLayerMarkedRawMoment_swap
    (beta : Real) (n : Nat) (a b : Real) (F : Real -> Real -> Real) :
    oddPrismThreeLayerMarkedRawMoment beta n a b F =
      oddPrismThreeLayerMarkedRawMoment beta n b a (fun x y => F y x) := by
  unfold oddPrismThreeLayerMarkedRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem oddPrismTransferBridgeRawMoment_eq_finiteExpMoment
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      finiteExpMoment (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeRawMoment finiteExpMoment
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferPairBaseWeight oddPrismTransferPairInteraction
    oddPrismPureSeamKernel
  rfl

theorem oddPrismTransferBridgeRawFirst_eq_finiteExpFirst
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawFirst beta n r =
      finiteExpFirst (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeRawFirst finiteExpFirst
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferPairBaseWeight oddPrismTransferPairInteraction
    oddPrismPureSeamKernel
  ring

theorem oddPrismTransferBridgeRawSecond_eq_finiteExpSecond
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawSecond beta n r =
      finiteExpSecond (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeRawSecond finiteExpSecond
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferPairBaseWeight oddPrismTransferPairInteraction
    oddPrismPureSeamKernel
  ring

theorem oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVarianceSkewNumerator beta n r =
      finiteExpVarianceSkew (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeVarianceSkewNumerator
    oddPrismTransferBridgeVarianceNumerator finiteExpVarianceSkew
  rw [oddPrismTransferBridgeRawMoment_eq_finiteExpMoment,
    oddPrismTransferBridgeRawMoment_eq_finiteExpMoment,
    oddPrismTransferBridgeRawFirst_eq_finiteExpFirst,
    oddPrismTransferBridgeRawFirst_eq_finiteExpFirst,
    oddPrismTransferBridgeRawSecond_eq_finiteExpSecond,
    oddPrismTransferBridgeRawSecond_eq_finiteExpSecond]


theorem two_mul_oddPrismTransferBridgeVarianceSkewNumerator_eq_fourStateSum
    (beta : Real) (n : Nat) (r : Real) :
    2 * oddPrismTransferBridgeVarianceSkewNumerator beta n r =
      let w := oddPrismTransferPairBaseWeight beta n
      let I := oddPrismTransferPairInteraction n
      ∑ x, ∑ y, ∑ z, ∑ q,
        w x * w y * w z * w q * (I x - I y) ^ 2 *
          (Real.exp (r * (I x + I y - I z - I q)) -
            Real.exp (-r * (I x + I y - I z - I q))) := by
  rw [oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp]
  exact two_mul_finiteExpVarianceSkew_eq_fourStateSum
    (oddPrismTransferPairBaseWeight beta n)
    (oddPrismTransferPairInteraction n) r






theorem finiteMarginal_logSupermodular
    {A B : Type*} [Fintype A] [Fintype B]
    [DistribLattice A] [DistribLattice B]
    (F : A × B -> Real) (hF : 0 <= F)
    (hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y))
    (x y : A) :
    (∑ b, F (x, b)) * (∑ b, F (y, b)) <=
      (∑ b, F (x ⊓ y, b)) * (∑ b, F (x ⊔ y, b)) := by
  apply four_functions_theorem_univ
  · exact fun b => hF (x, b)
  · exact fun b => hF (y, b)
  · exact fun b => hF (x ⊓ y, b)
  · exact fun b => hF (x ⊔ y, b)
  · intro b c
    simpa only [Prod.inf_def, Prod.sup_def] using
      (hlog (x, b) (y, c))



theorem rectangularLayerInternalInteraction_supermodular
    {m n : Nat} (s t : RectangularLayerConfig m n) :
    rectangularLayerInternalInteraction s +
        rectangularLayerInternalInteraction t <=
      rectangularLayerInternalInteraction (s ⊔ t) +
        rectangularLayerInternalInteraction (s ⊓ t) := by
  have hx :
      (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin s (⟨x.val, by omega⟩, y) *
            spin s (⟨x.val + 1, by omega⟩, y)) +
        (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin t (⟨x.val, by omega⟩, y) *
            spin t (⟨x.val + 1, by omega⟩, y)) <=
      (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin (s ⊔ t) (⟨x.val, by omega⟩, y) *
            spin (s ⊔ t) (⟨x.val + 1, by omega⟩, y)) +
        (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin (s ⊓ t) (⟨x.val, by omega⟩, y) *
            spin (s ⊓ t) (⟨x.val + 1, by omega⟩, y)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    simpa only [bond_mk] using
      (ifk_bond_supermodular s t
        s((⟨x.val, by omega⟩, y), (⟨x.val + 1, by omega⟩, y)))
  have hy :
      (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin s (x, ⟨y.val, by omega⟩) *
            spin s (x, ⟨y.val + 1, by omega⟩)) +
        (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin t (x, ⟨y.val, by omega⟩) *
            spin t (x, ⟨y.val + 1, by omega⟩)) <=
      (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin (s ⊔ t) (x, ⟨y.val, by omega⟩) *
            spin (s ⊔ t) (x, ⟨y.val + 1, by omega⟩)) +
        (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin (s ⊓ t) (x, ⟨y.val, by omega⟩) *
            spin (s ⊓ t) (x, ⟨y.val + 1, by omega⟩)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    simpa only [bond_mk] using
      (ifk_bond_supermodular s t
        s((x, ⟨y.val, by omega⟩), (x, ⟨y.val + 1, by omega⟩)))
  unfold rectangularLayerInternalInteraction
  linarith


theorem rectangularLayerBoundaryInteraction_modular
    {m n : Nat} (s t : RectangularLayerConfig m n) :
    (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin s p) +
        (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin t p) =
      (∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin (s ⊔ t) p) +
        ∑ p : Fin m × Fin n,
          rectangularLayerBoundaryDegree p * spin (s ⊓ t) p := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hp := ifk_spin_modular s t p
  nlinarith



theorem rectangularLayerBoltzmannInteraction_supermodular
    {beta : Real} (hbeta : 0 <= beta) {m n : Nat}
    (s t : RectangularLayerConfig m n) :
    rectangularLayerBoltzmannInteraction 1 beta s +
        rectangularLayerBoltzmannInteraction 1 beta t <=
      rectangularLayerBoltzmannInteraction 1 beta (s ⊔ t) +
        rectangularLayerBoltzmannInteraction 1 beta (s ⊓ t) := by
  have hi := rectangularLayerInternalInteraction_supermodular s t
  have hb := rectangularLayerBoundaryInteraction_modular s t
  unfold rectangularLayerBoltzmannInteraction
  norm_num
  nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hi)]


theorem oddPrismLayerHalfWeight_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerHalfWeight beta n s * oddPrismLayerHalfWeight beta n t <=
      oddPrismLayerHalfWeight beta n (s ⊔ t) *
        oddPrismLayerHalfWeight beta n (s ⊓ t) := by
  unfold oddPrismLayerHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := rectangularLayerBoltzmannInteraction_supermodular hbeta s t
  linarith




theorem oddPrismLayerSeamInteraction_pair_supermodular
    (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s v +
        oddPrismLayerSeamInteraction n t w <=
      oddPrismLayerSeamInteraction n (s ⊔ t) (v ⊔ w) +
        oddPrismLayerSeamInteraction n (s ⊓ t) (v ⊓ w) := by
  let a : ConfigSpace
      (Sum (Fin (2 * n + 1) × Fin (2 * n + 1))
        (Fin (2 * n + 1) × Fin (2 * n + 1))) := Sum.elim s v
  let b : ConfigSpace
      (Sum (Fin (2 * n + 1) × Fin (2 * n + 1))
        (Fin (2 * n + 1) × Fin (2 * n + 1))) := Sum.elim t w
  unfold oddPrismLayerSeamInteraction
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hp := ifk_bond_supermodular a b s(Sum.inl p, Sum.inr p)
  simpa only [bond_mk, a, b] using hp



theorem oddPrismPureSeamKernel_pair_logSupermodular
    {r : Real} (hr : 0 <= r) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n s v * oddPrismPureSeamKernel r n t w <=
      oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) *
        oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) := by
  unfold oddPrismPureSeamKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := oddPrismLayerSeamInteraction_pair_supermodular n s t v w
  nlinarith [mul_nonneg hr (sub_nonneg.mpr h)]




theorem oddPrismTiltedSeamTransfer_pair_logSupermodular
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTiltedSeamTransfer beta n r s v *
        oddPrismTiltedSeamTransfer beta n r t w <=
      oddPrismTiltedSeamTransfer beta n r (s ⊔ t) (v ⊔ w) *
        oddPrismTiltedSeamTransfer beta n r (s ⊓ t) (v ⊓ w) := by
  have hs := oddPrismLayerHalfWeight_logSupermodular hbeta n s t
  have hv := oddPrismLayerHalfWeight_logSupermodular hbeta n v w
  have hk := oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w
  have hs0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLayerHalfWeight beta n a :=
    (oddPrismLayerHalfWeight_pos beta n a).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel r n a b :=
    (oddPrismPureSeamKernel_pos r n a b).le
  unfold oddPrismTiltedSeamTransfer
  calc
    (oddPrismLayerHalfWeight beta n s * oddPrismPureSeamKernel r n s v *
          oddPrismLayerHalfWeight beta n v) *
        (oddPrismLayerHalfWeight beta n t * oddPrismPureSeamKernel r n t w *
          oddPrismLayerHalfWeight beta n w) =
      (oddPrismLayerHalfWeight beta n s * oddPrismLayerHalfWeight beta n t) *
        (oddPrismPureSeamKernel r n s v * oddPrismPureSeamKernel r n t w) *
        (oddPrismLayerHalfWeight beta n v * oddPrismLayerHalfWeight beta n w) := by ring
    _ <=
      (oddPrismLayerHalfWeight beta n (s ⊔ t) *
          oddPrismLayerHalfWeight beta n (s ⊓ t)) *
        (oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w)) *
        (oddPrismLayerHalfWeight beta n (v ⊔ w) *
          oddPrismLayerHalfWeight beta n (v ⊓ w)) := by
            gcongr
            · exact mul_nonneg (hs0 v) (hs0 w)
            · exact mul_nonneg
                (mul_nonneg (hs0 (s ⊔ t)) (hs0 (s ⊓ t)))
                (mul_nonneg (hk0 (s ⊔ t) (v ⊔ w))
                  (hk0 (s ⊓ t) (v ⊓ w)))
            · exact mul_nonneg (hk0 s v) (hk0 t w)
            · exact mul_nonneg (hs0 (s ⊔ t)) (hs0 (s ⊓ t))
    _ =
      (oddPrismLayerHalfWeight beta n (s ⊔ t) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) *
          oddPrismLayerHalfWeight beta n (v ⊔ w)) *
        (oddPrismLayerHalfWeight beta n (s ⊓ t) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
          oddPrismLayerHalfWeight beta n (v ⊓ w)) := by ring


theorem rectangularLayerFaceBoundary_modular
    (beta : Real) {m n : Nat} (s t : RectangularLayerConfig m n) :
    rectangularLayerFaceBoundary 1 beta s +
        rectangularLayerFaceBoundary 1 beta t =
      rectangularLayerFaceBoundary 1 beta (s ⊔ t) +
        rectangularLayerFaceBoundary 1 beta (s ⊓ t) := by
  unfold rectangularLayerFaceBoundary
  norm_num
  rw [← mul_add, ← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact ifk_spin_modular s t p



theorem rectangularPrismTransferBoundaryVector_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) s *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) t <=
      rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (s ⊓ t) *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (s ⊔ t) := by
  unfold rectangularPrismTransferBoundaryVector
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi := rectangularLayerBoltzmannInteraction_supermodular hbeta s t
  have hf := rectangularLayerFaceBoundary_modular beta s t
  linarith



theorem transferTailPathWeight_logSupermodular
    {E : Type*} [Fintype E] [DistribLattice E]
    (A : Matrix E E Real) (a : E -> Real)
    (ha0 : 0 <= a) (hA0 : ∀ x y, 0 <= A x y)
    (ha : ∀ x y, a x * a y <= a (x ⊓ y) * a (x ⊔ y))
    (hA : ∀ x y u v,
      A x u * A y v <= A (x ⊓ y) (u ⊓ v) * A (x ⊔ y) (u ⊔ v))
    (k : Nat) (q r : Fin (k + 1) -> E) :
    transferTailPathWeight A a k q * transferTailPathWeight A a k r <=
      transferTailPathWeight A a k (q ⊓ r) *
        transferTailPathWeight A a k (q ⊔ r) := by
  have hp :
      (∏ j : Fin k, A (q j.castSucc) (q j.succ)) *
          (∏ j : Fin k, A (r j.castSucc) (r j.succ)) <=
        (∏ j : Fin k, A ((q ⊓ r) j.castSucc) ((q ⊓ r) j.succ)) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro j _
      exact mul_nonneg (hA0 _ _) (hA0 _ _)
    · intro j _
      simpa only [Pi.inf_apply, Pi.sup_apply] using
        hA (q j.castSucc) (r j.castSucc) (q j.succ) (r j.succ)
  unfold transferTailPathWeight
  calc
    (a (q 0) * ∏ j : Fin k, A (q j.castSucc) (q j.succ)) *
        (a (r 0) * ∏ j : Fin k, A (r j.castSucc) (r j.succ)) =
      (a (q 0) * a (r 0)) *
        ((∏ j : Fin k, A (q j.castSucc) (q j.succ)) *
          ∏ j : Fin k, A (r j.castSucc) (r j.succ)) := by ring
    _ <= (a ((q ⊓ r) 0) * a ((q ⊔ r) 0)) *
        ((∏ j : Fin k, A ((q ⊓ r) j.castSucc) ((q ⊓ r) j.succ)) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by
      apply mul_le_mul
      · simpa only [Pi.inf_apply, Pi.sup_apply] using ha (q 0) (r 0)
      · exact hp
      · exact mul_nonneg
          (Finset.prod_nonneg fun j _ => hA0 _ _)
          (Finset.prod_nonneg fun j _ => hA0 _ _)
      · exact mul_nonneg (ha0 _) (ha0 _)
    _ =
      (a ((q ⊓ r) 0) *
          ∏ j : Fin k, A ((q ⊓ r) j.castSucc) ((q ⊓ r) j.succ)) *
        (a ((q ⊔ r) 0) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by ring


theorem sum_transferTailPathWeight_fixed_endpoint
    {E : Type*} [Fintype E] [DecidableEq E]
    (A : Matrix E E Real) (hA : A.IsHermitian) (a : E -> Real)
    (k : Nat) (s : E) :
    (∑ q : Fin k -> E,
      transferTailPathWeight A a k (Fin.snoc q s)) = ((A ^ k) *ᵥ a) s := by
  let f : E -> Real := fun t => if t = s then 1 else 0
  have h := sum_transferTailPathWeight_mul_endpoint A hA a f k
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (k + 1) => E)] at h
  rw [Fintype.sum_prod_type] at h
  simpa [Fin.snocEquiv, f] using h



def oddPrismUpperSlabPathWeight (beta : Real) (n k : Nat)
    (q : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  transferTailPathWeight A a k q *
    oddPrismLayerHalfWeight beta n (q (Fin.last k))


def oddPrismUpperSlabEndpointMarginal (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  ∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
    oddPrismUpperSlabPathWeight beta n k (Fin.snoc q s)



theorem oddPrismUpperSlabEndpointMarginal_eq_conditioned
    (beta : Real) (n : Nat) :
    oddPrismUpperSlabEndpointMarginal beta n (n - 1) =
      oddPrismUpperConditionedVector beta n := by
  funext s
  unfold oddPrismUpperSlabEndpointMarginal oddPrismUpperSlabPathWeight
    oddPrismUpperConditionedVector oddPrismUpperTransferTail
  simp only [Fin.snoc_last]
  rw [← Finset.sum_mul]
  rw [sum_transferTailPathWeight_fixed_endpoint]
  · ring
  · exact rectangularPrismTransfer_isHermitian
      1 beta (2 * n + 1) (2 * n + 1)



theorem oddPrismUpperSlabPathWeight_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (q r : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabPathWeight beta n k q *
        oddPrismUpperSlabPathWeight beta n k r <=
      oddPrismUpperSlabPathWeight beta n k (q ⊓ r) *
        oddPrismUpperSlabPathWeight beta n k (q ⊔ r) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  have ha0 : 0 <= a := fun s =>
    (rectangularPrismTransferBoundaryVector_pos
      1 beta (2 * n + 1) (2 * n + 1) s).le
  have hA0 : ∀ s t, 0 <= A s t := fun s t =>
    (rectangularPrismTransfer_pos
      1 beta (2 * n + 1) (2 * n + 1) s t).le
  have ha : ∀ s t, a s * a t <= a (s ⊓ t) * a (s ⊔ t) := by
    intro s t
    exact rectangularPrismTransferBoundaryVector_logSupermodular hbeta n s t
  have hA : ∀ s t v w,
      A s v * A t w <= A (s ⊓ t) (v ⊓ w) * A (s ⊔ t) (v ⊔ w) := by
    intro s t v w
    change rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) s v *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) t w <=
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (s ⊓ t) (v ⊓ w) *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (s ⊔ t) (v ⊔ w)
    rw [← oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n]
    simpa only [mul_comm] using
      (oddPrismTiltedSeamTransfer_pair_logSupermodular
        hbeta hbeta n s t v w)
  have htail := transferTailPathWeight_logSupermodular
    A a ha0 hA0 ha hA k q r
  have hend :
      oddPrismLayerHalfWeight beta n (q (Fin.last k)) *
          oddPrismLayerHalfWeight beta n (r (Fin.last k)) <=
        oddPrismLayerHalfWeight beta n ((q ⊓ r) (Fin.last k)) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k)) := by
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_comm] using
      (oddPrismLayerHalfWeight_logSupermodular hbeta n
        (q (Fin.last k)) (r (Fin.last k)))
  have htail0 (p : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= transferTailPathWeight A a k p := by
    unfold transferTailPathWeight
    exact mul_nonneg (ha0 _) (Finset.prod_nonneg fun j _ => hA0 _ _)
  unfold oddPrismUpperSlabPathWeight
  change (transferTailPathWeight A a k q *
      oddPrismLayerHalfWeight beta n (q (Fin.last k))) *
    (transferTailPathWeight A a k r *
      oddPrismLayerHalfWeight beta n (r (Fin.last k))) <= _
  calc
    (transferTailPathWeight A a k q *
          oddPrismLayerHalfWeight beta n (q (Fin.last k))) *
        (transferTailPathWeight A a k r *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) =
      (transferTailPathWeight A a k q * transferTailPathWeight A a k r) *
        (oddPrismLayerHalfWeight beta n (q (Fin.last k)) *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) := by ring
    _ <=
      (transferTailPathWeight A a k (q ⊓ r) *
          transferTailPathWeight A a k (q ⊔ r)) *
        (oddPrismLayerHalfWeight beta n ((q ⊓ r) (Fin.last k)) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by
      apply mul_le_mul htail hend
      · exact mul_nonneg
          (oddPrismLayerHalfWeight_pos beta n _).le
          (oddPrismLayerHalfWeight_pos beta n _).le
      · exact mul_nonneg (htail0 (q ⊓ r)) (htail0 (q ⊔ r))
    _ =
      (transferTailPathWeight A a k (q ⊓ r) *
          oddPrismLayerHalfWeight beta n ((q ⊓ r) (Fin.last k))) *
        (transferTailPathWeight A a k (q ⊔ r) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by ring



theorem oddPrismUpperSlabEndpointMarginal_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabEndpointMarginal beta n k s *
        oddPrismUpperSlabEndpointMarginal beta n k t <=
      oddPrismUpperSlabEndpointMarginal beta n k (s ⊓ t) *
        oddPrismUpperSlabEndpointMarginal beta n k (s ⊔ t) := by
  let F : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) -> Real :=
    fun p => oddPrismUpperSlabPathWeight beta n k (Fin.snoc p.2 p.1)
  have hF : 0 <= F := by
    intro p
    unfold F oddPrismUpperSlabPathWeight transferTailPathWeight
    exact mul_nonneg
      (mul_nonneg
        (rectangularPrismTransferBoundaryVector_pos
          1 beta (2 * n + 1) (2 * n + 1) _).le
        (Finset.prod_nonneg fun j _ =>
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) _ _).le))
      (oddPrismLayerHalfWeight_pos beta n _).le
  have hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y) := by
    intro x y
    obtain ⟨s, q⟩ := x
    obtain ⟨t, r⟩ := y
    have hpath := oddPrismUpperSlabPathWeight_logSupermodular
      hbeta n k (Fin.snoc q s) (Fin.snoc r t)
    have hinf : Fin.snoc q s ⊓ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊓ r) (s ⊓ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
    have hsup : Fin.snoc q s ⊔ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊔ r) (s ⊔ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
    rw [hinf, hsup] at hpath
    exact hpath
  exact finiteMarginal_logSupermodular F hF hlog s t



theorem oddPrismUpperConditionedVector_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperConditionedVector beta n s *
        oddPrismUpperConditionedVector beta n t <=
      oddPrismUpperConditionedVector beta n (s ⊓ t) *
        oddPrismUpperConditionedVector beta n (s ⊔ t) := by
  rw [← oddPrismUpperSlabEndpointMarginal_eq_conditioned beta n]
  exact oddPrismUpperSlabEndpointMarginal_logSupermodular hbeta n (n - 1) s t



def oddPrismUpperOneStepMarginal (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  ∑ v, oddPrismPureSeamKernel beta n s v *
    oddPrismUpperConditionedVector beta n v


theorem oddPrismUpperOneStepMarginal_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperOneStepMarginal beta n s *
        oddPrismUpperOneStepMarginal beta n t <=
      oddPrismUpperOneStepMarginal beta n (s ⊓ t) *
        oddPrismUpperOneStepMarginal beta n (s ⊔ t) := by
  let F : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real :=
    fun p => oddPrismPureSeamKernel beta n p.1 p.2 *
      oddPrismUpperConditionedVector beta n p.2
  have hF : 0 <= F := by
    intro p
    exact mul_nonneg (oddPrismPureSeamKernel_pos beta n _ _).le
      (oddPrismUpperConditionedVector_pos beta n _).le
  have hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y) := by
    intro x y
    obtain ⟨s, v⟩ := x
    obtain ⟨t, w⟩ := y
    have hk := oddPrismPureSeamKernel_pair_logSupermodular
      hbeta n s t v w
    have hu := oddPrismUpperConditionedVector_logSupermodular
      hbeta n v w
    have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
        0 <= oddPrismPureSeamKernel beta n a b :=
      (oddPrismPureSeamKernel_pos beta n a b).le
    have hu0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
        0 <= oddPrismUpperConditionedVector beta n a :=
      (oddPrismUpperConditionedVector_pos beta n a).le
    unfold F
    calc
      (oddPrismPureSeamKernel beta n s v *
          oddPrismUpperConditionedVector beta n v) *
        (oddPrismPureSeamKernel beta n t w *
          oddPrismUpperConditionedVector beta n w) =
        (oddPrismPureSeamKernel beta n s v *
          oddPrismPureSeamKernel beta n t w) *
        (oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n w) := by ring
      _ <=
        (oddPrismPureSeamKernel beta n (s ⊓ t) (v ⊓ w) *
          oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w)) *
        (oddPrismUpperConditionedVector beta n (v ⊓ w) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by
        apply mul_le_mul
        · simpa only [mul_comm] using hk
        · exact hu
        · exact mul_nonneg (hu0 v) (hu0 w)
        · exact mul_nonneg
            (hk0 (s ⊓ t) (v ⊓ w)) (hk0 (s ⊔ t) (v ⊔ w))
      _ =
        (oddPrismPureSeamKernel beta n (s ⊓ t) (v ⊓ w) *
          oddPrismUpperConditionedVector beta n (v ⊓ w)) *
        (oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by ring
  exact finiteMarginal_logSupermodular F hF hlog s t



theorem oddPrismLowerConditionedVector_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLowerConditionedVector beta n s *
        oddPrismLowerConditionedVector beta n t <=
      oddPrismLowerConditionedVector beta n (s ⊓ t) *
        oddPrismLowerConditionedVector beta n (s ⊔ t) := by
  rw [oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s,
    oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn t,
    oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn (s ⊓ t),
    oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn (s ⊔ t)]
  change (oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperOneStepMarginal beta n s) *
    (oddPrismLayerHalfWeight beta n t ^ 2 *
      oddPrismUpperOneStepMarginal beta n t) <= _
  have hh := oddPrismLayerHalfWeight_logSupermodular hbeta n s t
  have hh2 :
      oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismLayerHalfWeight beta n t ^ 2 <=
        oddPrismLayerHalfWeight beta n (s ⊓ t) ^ 2 *
          oddPrismLayerHalfWeight beta n (s ⊔ t) ^ 2 := by
    have h0 : 0 <= oddPrismLayerHalfWeight beta n s *
        oddPrismLayerHalfWeight beta n t := mul_nonneg
      (oddPrismLayerHalfWeight_pos beta n s).le
      (oddPrismLayerHalfWeight_pos beta n t).le
    have h1 : 0 <= oddPrismLayerHalfWeight beta n (s ⊓ t) *
        oddPrismLayerHalfWeight beta n (s ⊔ t) := mul_nonneg
      (oddPrismLayerHalfWeight_pos beta n _).le
      (oddPrismLayerHalfWeight_pos beta n _).le
    nlinarith
  have hm := oddPrismUpperOneStepMarginal_logSupermodular hbeta n s t
  have hm0 (u : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismUpperOneStepMarginal beta n u := by
    unfold oddPrismUpperOneStepMarginal
    exact Finset.sum_nonneg fun v _ => mul_nonneg
      (oddPrismPureSeamKernel_pos beta n u v).le
      (oddPrismUpperConditionedVector_pos beta n v).le
  calc
    (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperOneStepMarginal beta n s) *
        (oddPrismLayerHalfWeight beta n t ^ 2 *
          oddPrismUpperOneStepMarginal beta n t) =
      (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismLayerHalfWeight beta n t ^ 2) *
        (oddPrismUpperOneStepMarginal beta n s *
          oddPrismUpperOneStepMarginal beta n t) := by ring
    _ <=
      (oddPrismLayerHalfWeight beta n (s ⊓ t) ^ 2 *
          oddPrismLayerHalfWeight beta n (s ⊔ t) ^ 2) *
        (oddPrismUpperOneStepMarginal beta n (s ⊓ t) *
          oddPrismUpperOneStepMarginal beta n (s ⊔ t)) := by
      apply mul_le_mul hh2 hm
      · exact mul_nonneg (hm0 s) (hm0 t)
      · positivity
    _ =
      (oddPrismLayerHalfWeight beta n (s ⊓ t) ^ 2 *
          oddPrismUpperOneStepMarginal beta n (s ⊓ t)) *
        (oddPrismLayerHalfWeight beta n (s ⊔ t) ^ 2 *
          oddPrismUpperOneStepMarginal beta n (s ⊔ t)) := by ring



theorem oddPrismTransferPairBaseWeight_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferPairBaseWeight beta n x *
        oddPrismTransferPairBaseWeight beta n y <=
      oddPrismTransferPairBaseWeight beta n (x ⊓ y) *
        oddPrismTransferPairBaseWeight beta n (x ⊔ y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hl := oddPrismLowerConditionedVector_logSupermodular
    hbeta n hn s t
  have hu := oddPrismUpperConditionedVector_logSupermodular
    hbeta n v w
  have hl0 (u : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLowerConditionedVector beta n u := by
    unfold oddPrismLowerConditionedVector
    exact mul_nonneg (oddPrismLayerHalfWeight_pos beta n u).le
      (rectangularPrismTransfer_pow_mulVec_boundary_pos beta n n u).le
  have hu0 (u : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismUpperConditionedVector beta n u :=
    (oddPrismUpperConditionedVector_pos beta n u).le
  unfold oddPrismTransferPairBaseWeight
  calc
    (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n v) *
        (oddPrismLowerConditionedVector beta n t *
          oddPrismUpperConditionedVector beta n w) =
      (oddPrismLowerConditionedVector beta n s *
          oddPrismLowerConditionedVector beta n t) *
        (oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n w) := by ring
    _ <=
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismLowerConditionedVector beta n (s ⊔ t)) *
        (oddPrismUpperConditionedVector beta n (v ⊓ w) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by
      apply mul_le_mul hl hu
      · exact mul_nonneg (hu0 v) (hu0 w)
      · exact mul_nonneg (hl0 (s ⊓ t)) (hl0 (s ⊔ t))
    _ =
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismUpperConditionedVector beta n (v ⊓ w)) *
        (oddPrismLowerConditionedVector beta n (s ⊔ t) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by ring

theorem oddPrismLowerConditionedVector_pos
    (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismLowerConditionedVector beta n s := by
  unfold oddPrismLowerConditionedVector oddPrismLowerTransferTail
  exact mul_pos (oddPrismLayerHalfWeight_pos beta n s)
    (rectangularPrismTransfer_pow_mulVec_boundary_pos beta n n s)

theorem oddPrismTransferPairBaseWeight_pos
    (beta : Real) (n : Nat)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismTransferPairBaseWeight beta n x := by
  exact mul_pos (oddPrismLowerConditionedVector_pos beta n x.1)
    (oddPrismUpperConditionedVector_pos beta n x.2)


def oddPrismTransferTiltedPairWeight
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  oddPrismTransferPairBaseWeight beta n x *
    oddPrismPureSeamKernel r n x.1 x.2

theorem oddPrismTransferTiltedPairWeight_pos
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismTransferTiltedPairWeight beta n r x := by
  exact mul_pos (oddPrismTransferPairBaseWeight_pos beta n x)
    (oddPrismPureSeamKernel_pos r n x.1 x.2)



theorem oddPrismTransferTiltedPairWeight_logSupermodular
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferTiltedPairWeight beta n r y <=
      oddPrismTransferTiltedPairWeight beta n r (x ⊓ y) *
        oddPrismTransferTiltedPairWeight beta n r (x ⊔ y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hb := oddPrismTransferPairBaseWeight_logSupermodular
    hbeta n hn (s, v) (t, w)
  have hk := oddPrismPureSeamKernel_pair_logSupermodular
    hr n s t v w
  have hb0 (z : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismTransferPairBaseWeight beta n z :=
    (oddPrismTransferPairBaseWeight_pos beta n z).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel r n a b :=
    (oddPrismPureSeamKernel_pos r n a b).le
  unfold oddPrismTransferTiltedPairWeight
  calc
    (oddPrismTransferPairBaseWeight beta n (s, v) *
          oddPrismPureSeamKernel r n s v) *
        (oddPrismTransferPairBaseWeight beta n (t, w) *
          oddPrismPureSeamKernel r n t w) =
      (oddPrismTransferPairBaseWeight beta n (s, v) *
          oddPrismTransferPairBaseWeight beta n (t, w)) *
        (oddPrismPureSeamKernel r n s v *
          oddPrismPureSeamKernel r n t w) := by ring
    _ <=
      (oddPrismTransferPairBaseWeight beta n ((s, v) ⊓ (t, w)) *
          oddPrismTransferPairBaseWeight beta n ((s, v) ⊔ (t, w))) *
        (oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by
      apply mul_le_mul
      · exact hb
      · simpa only [mul_comm] using hk
      · exact mul_nonneg (hk0 s v) (hk0 t w)
      · exact mul_nonneg (hb0 ((s, v) ⊓ (t, w)))
          (hb0 ((s, v) ⊔ (t, w)))
    _ =
      (oddPrismTransferPairBaseWeight beta n ((s, v) ⊓ (t, w)) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w)) *
        (oddPrismTransferPairBaseWeight beta n ((s, v) ⊔ (t, w)) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by ring

theorem oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ x, oddPrismTransferTiltedPairWeight beta n r x := by
  unfold oddPrismTransferBridgeRawMoment oddPrismTransferTiltedPairWeight
    oddPrismTransferPairBaseWeight
  rw [Fintype.sum_prod_type]



@[simp] theorem flipV_inf {V : Type*} (s t : ConfigSpace V) :
    FieldGhostDict.flipV (s ⊓ t) =
      FieldGhostDict.flipV s ⊔ FieldGhostDict.flipV t := by
  funext p
  by_cases hs : s p <;> by_cases ht : t p <;>
    simp [FieldGhostDict.flipV, hs, ht]

@[simp] theorem flipV_sup {V : Type*} (s t : ConfigSpace V) :
    FieldGhostDict.flipV (s ⊔ t) =
      FieldGhostDict.flipV s ⊓ FieldGhostDict.flipV t := by
  funext p
  by_cases hs : s p <;> by_cases ht : t p <;>
    simp [FieldGhostDict.flipV, hs, ht]

theorem rectangularLayerInternalInteraction_flip
    {m n : Nat} (s : RectangularLayerConfig m n) :
    rectangularLayerInternalInteraction (FieldGhostDict.flipV s) =
      rectangularLayerInternalInteraction s := by
  unfold rectangularLayerInternalInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  ring

theorem spin_neg_add_le_inf_sup
    {V : Type*} (s t : ConfigSpace V) (p : V) :
    -spin s p + spin t p <= -spin (s ⊓ t) p + spin (s ⊔ t) p := by
  by_cases hs : s p <;> by_cases ht : t p <;>
    simp [spin, hs, ht] <;> norm_num

theorem rectangularLayerBoundaryInteraction_flip
    {m n : Nat} (s : RectangularLayerConfig m n) :
    (∑ p : Fin m × Fin n,
      rectangularLayerBoundaryDegree p * spin (FieldGhostDict.flipV s) p) =
      -∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin s p := by
  simp_rw [FieldGhostDict.spin_flipV, mul_neg]
  rw [Finset.sum_neg_distrib]

theorem rectangularLayerBoundaryInteraction_cross
    {m n : Nat} (s t : RectangularLayerConfig m n) :
    -(∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin s p) +
        ∑ p : Fin m × Fin n,
          rectangularLayerBoundaryDegree p * spin t p <=
      -(∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin (s ⊓ t) p) +
        ∑ p : Fin m × Fin n,
          rectangularLayerBoundaryDegree p * spin (s ⊔ t) p := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hp := spin_neg_add_le_inf_sup s t p
  have hd : 0 <= (rectangularLayerBoundaryDegree p : Real) := Nat.cast_nonneg _
  nlinarith


theorem rectangularLayerBoltzmannInteraction_flip_cross
    {beta : Real} (hbeta : 0 <= beta) {m n : Nat}
    (s t : RectangularLayerConfig m n) :
    rectangularLayerBoltzmannInteraction 1 beta (FieldGhostDict.flipV s) +
        rectangularLayerBoltzmannInteraction 1 beta t <=
      rectangularLayerBoltzmannInteraction 1 beta
          (FieldGhostDict.flipV (s ⊓ t)) +
        rectangularLayerBoltzmannInteraction 1 beta (s ⊔ t) := by
  have hi := rectangularLayerInternalInteraction_supermodular s t
  have hb := rectangularLayerBoundaryInteraction_cross s t
  unfold rectangularLayerBoltzmannInteraction
  norm_num
  rw [← flipV_inf s t]
  rw [rectangularLayerInternalInteraction_flip,
    rectangularLayerInternalInteraction_flip,
    rectangularLayerBoundaryInteraction_flip,
    rectangularLayerBoundaryInteraction_flip]
  nlinarith [mul_nonneg hbeta (add_nonneg
    (sub_nonneg.mpr hi) (sub_nonneg.mpr hb))]

theorem oddPrismLayerHalfWeight_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) *
        oddPrismLayerHalfWeight beta n t <=
      oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) *
        oddPrismLayerHalfWeight beta n (s ⊔ t) := by
  unfold oddPrismLayerHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := rectangularLayerBoltzmannInteraction_flip_cross hbeta s t
  linarith

theorem rectangularLayerFaceBoundary_flip
    (beta : Real) {m n : Nat} (s : RectangularLayerConfig m n) :
    rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV s) =
      -rectangularLayerFaceBoundary 1 beta s := by
  unfold rectangularLayerFaceBoundary
  norm_num
  simp_rw [FieldGhostDict.spin_flipV]
  rw [Finset.sum_neg_distrib]
  ring

theorem rectangularLayerFaceBoundary_flip_cross
    {beta : Real} (hbeta : 0 <= beta) {m n : Nat}
    (s t : RectangularLayerConfig m n) :
    rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV s) +
        rectangularLayerFaceBoundary 1 beta t <=
      rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV (s ⊓ t)) +
        rectangularLayerFaceBoundary 1 beta (s ⊔ t) := by
  have hs :
      -(∑ p : Fin m × Fin n, spin s p) +
          ∑ p : Fin m × Fin n, spin t p <=
        -(∑ p : Fin m × Fin n, spin (s ⊓ t) p) +
          ∑ p : Fin m × Fin n, spin (s ⊔ t) p := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => spin_neg_add_le_inf_sup s t p
  rw [rectangularLayerFaceBoundary_flip,
    rectangularLayerFaceBoundary_flip]
  unfold rectangularLayerFaceBoundary
  norm_num
  nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hs)]

theorem rectangularPrismTransferBoundaryVector_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV s) *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) t <=
      rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV (s ⊓ t)) *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (s ⊔ t) := by
  unfold rectangularPrismTransferBoundaryVector
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi := rectangularLayerBoltzmannInteraction_flip_cross hbeta s t
  have hf := rectangularLayerFaceBoundary_flip_cross hbeta s t
  linarith

@[simp] theorem oddPrismLayerSeamInteraction_flip_both
    (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n (FieldGhostDict.flipV s)
        (FieldGhostDict.flipV t) = oddPrismLayerSeamInteraction n s t := by
  unfold oddPrismLayerSeamInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  apply Finset.sum_congr rfl
  intro p _
  ring

@[simp] theorem oddPrismPureSeamKernel_flip_both
    (r : Real) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n (FieldGhostDict.flipV s)
        (FieldGhostDict.flipV t) = oddPrismPureSeamKernel r n s t := by
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_flip_both]

theorem oddPrismPureSeamKernel_flip_cross
    {r : Real} (hr : 0 <= r) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n (FieldGhostDict.flipV s)
          (FieldGhostDict.flipV v) *
        oddPrismPureSeamKernel r n t w <=
      oddPrismPureSeamKernel r n (FieldGhostDict.flipV (s ⊓ t))
          (FieldGhostDict.flipV (v ⊓ w)) *
        oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) := by
  simp only [oddPrismPureSeamKernel_flip_both]
  simpa only [mul_comm] using
    (oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w)

theorem rectangularPrismTransfer_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (FieldGhostDict.flipV s) (FieldGhostDict.flipV v) *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) t w <=
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (FieldGhostDict.flipV (s ⊓ t)) (FieldGhostDict.flipV (v ⊓ w)) *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (s ⊔ t) (v ⊔ w) := by
  rw [← oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n]
  unfold oddPrismTiltedSeamTransfer
  have hs := oddPrismLayerHalfWeight_flip_cross hbeta n s t
  have hv := oddPrismLayerHalfWeight_flip_cross hbeta n v w
  have hk := oddPrismPureSeamKernel_flip_cross hbeta n s t v w
  have hh0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLayerHalfWeight beta n a :=
    (oddPrismLayerHalfWeight_pos beta n a).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel beta n a b :=
    (oddPrismPureSeamKernel_pos beta n a b).le
  calc
    (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) *
          oddPrismPureSeamKernel beta n (FieldGhostDict.flipV s)
            (FieldGhostDict.flipV v) *
          oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV v)) *
        (oddPrismLayerHalfWeight beta n t *
          oddPrismPureSeamKernel beta n t w *
          oddPrismLayerHalfWeight beta n w) =
      (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) *
          oddPrismLayerHalfWeight beta n t) *
        (oddPrismPureSeamKernel beta n (FieldGhostDict.flipV s)
            (FieldGhostDict.flipV v) * oddPrismPureSeamKernel beta n t w) *
        (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV v) *
          oddPrismLayerHalfWeight beta n w) := by ring
    _ <=
      (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) *
          oddPrismLayerHalfWeight beta n (s ⊔ t)) *
        (oddPrismPureSeamKernel beta n (FieldGhostDict.flipV (s ⊓ t))
            (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w)) *
        (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismLayerHalfWeight beta n (v ⊔ w)) := by
      gcongr
      · exact mul_nonneg (hh0 _) (hh0 _)
      · exact mul_nonneg
          (mul_nonneg (hh0 _) (hh0 _)) (mul_nonneg (hk0 _ _) (hk0 _ _))
      · exact mul_nonneg (hk0 _ _) (hk0 _ _)
      · exact mul_nonneg (hh0 _) (hh0 _)
    _ =
      (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) *
          oddPrismPureSeamKernel beta n (FieldGhostDict.flipV (s ⊓ t))
            (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (v ⊓ w))) *
        (oddPrismLayerHalfWeight beta n (s ⊔ t) *
          oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w) *
          oddPrismLayerHalfWeight beta n (v ⊔ w)) := by ring



theorem finiteCrossMarginal
    {A B : Type*} [Fintype A] [Fintype B]
    [DistribLattice A] [DistribLattice B]
    (Fminus Fplus : A × B -> Real)
    (hminus : 0 <= Fminus) (hplus : 0 <= Fplus)
    (hcross : ∀ x y,
      Fminus x * Fplus y <=
        Fminus (x ⊓ y) * Fplus (x ⊔ y))
    (x y : A) :
    (∑ b, Fminus (x, b)) * (∑ b, Fplus (y, b)) <=
      (∑ b, Fminus (x ⊓ y, b)) *
        (∑ b, Fplus (x ⊔ y, b)) := by
  apply four_functions_theorem_univ
  · exact fun b => hminus (x, b)
  · exact fun b => hplus (y, b)
  · exact fun b => hminus (x ⊓ y, b)
  · exact fun b => hplus (x ⊔ y, b)
  · intro b c
    simpa only [Prod.inf_def, Prod.sup_def] using
      (hcross (x, b) (y, c))


def oddPrismFlipLayerPath {m n k : Nat}
    (q : Fin k -> RectangularLayerConfig m n) :
    Fin k -> RectangularLayerConfig m n :=
  fun j => FieldGhostDict.flipV (q j)

@[simp] theorem oddPrismFlipLayerPath_apply
    {m n k : Nat} (q : Fin k -> RectangularLayerConfig m n) (j : Fin k) :
    oddPrismFlipLayerPath q j = FieldGhostDict.flipV (q j) := rfl

@[simp] theorem oddPrismFlipLayerPath_involutive
    {m n k : Nat} (q : Fin k -> RectangularLayerConfig m n) :
    oddPrismFlipLayerPath (oddPrismFlipLayerPath q) = q := by
  funext j
  exact FieldGhostDict.flipV_involutive (q j)


theorem transferTailPathWeight_flip_cross
    {E : Type*} [Fintype E] [DistribLattice E]
    (flip : E -> E) (A : Matrix E E Real) (a : E -> Real)
    (ha0 : 0 <= a) (hA0 : ∀ x y, 0 <= A x y)
    (ha : ∀ x y,
      a (flip x) * a y <= a (flip (x ⊓ y)) * a (x ⊔ y))
    (hA : ∀ x y u v,
      A (flip x) (flip u) * A y v <=
        A (flip (x ⊓ y)) (flip (u ⊓ v)) * A (x ⊔ y) (u ⊔ v))
    (k : Nat) (q r : Fin (k + 1) -> E) :
    transferTailPathWeight A a k (fun j => flip (q j)) *
        transferTailPathWeight A a k r <=
      transferTailPathWeight A a k (fun j => flip ((q ⊓ r) j)) *
        transferTailPathWeight A a k (q ⊔ r) := by
  have hp :
      (∏ j : Fin k, A (flip (q j.castSucc)) (flip (q j.succ))) *
          (∏ j : Fin k, A (r j.castSucc) (r j.succ)) <=
        (∏ j : Fin k,
          A (flip ((q ⊓ r) j.castSucc)) (flip ((q ⊓ r) j.succ))) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro j _
      exact mul_nonneg (hA0 _ _) (hA0 _ _)
    · intro j _
      simpa only [Pi.inf_apply, Pi.sup_apply] using
        hA (q j.castSucc) (r j.castSucc) (q j.succ) (r j.succ)
  unfold transferTailPathWeight
  calc
    (a (flip (q 0)) *
          ∏ j : Fin k, A (flip (q j.castSucc)) (flip (q j.succ))) *
        (a (r 0) * ∏ j : Fin k, A (r j.castSucc) (r j.succ)) =
      (a (flip (q 0)) * a (r 0)) *
        ((∏ j : Fin k, A (flip (q j.castSucc)) (flip (q j.succ))) *
          ∏ j : Fin k, A (r j.castSucc) (r j.succ)) := by ring
    _ <=
      (a (flip ((q ⊓ r) 0)) * a ((q ⊔ r) 0)) *
        ((∏ j : Fin k,
          A (flip ((q ⊓ r) j.castSucc)) (flip ((q ⊓ r) j.succ))) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by
      apply mul_le_mul
      · simpa only [Pi.inf_apply, Pi.sup_apply] using ha (q 0) (r 0)
      · exact hp
      · exact mul_nonneg
          (Finset.prod_nonneg fun j _ => hA0 _ _)
          (Finset.prod_nonneg fun j _ => hA0 _ _)
      · exact mul_nonneg (ha0 _) (ha0 _)
    _ =
      (a (flip ((q ⊓ r) 0)) *
          ∏ j : Fin k,
            A (flip ((q ⊓ r) j.castSucc)) (flip ((q ⊓ r) j.succ))) *
        (a ((q ⊔ r) 0) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by ring

theorem oddPrismUpperSlabPathWeight_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (q r : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabPathWeight beta n k (oddPrismFlipLayerPath q) *
        oddPrismUpperSlabPathWeight beta n k r <=
      oddPrismUpperSlabPathWeight beta n k
          (oddPrismFlipLayerPath (q ⊓ r)) *
        oddPrismUpperSlabPathWeight beta n k (q ⊔ r) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  have ha0 : 0 <= a := fun s =>
    (rectangularPrismTransferBoundaryVector_pos
      1 beta (2 * n + 1) (2 * n + 1) s).le
  have hA0 : ∀ s t, 0 <= A s t := fun s t =>
    (rectangularPrismTransfer_pos
      1 beta (2 * n + 1) (2 * n + 1) s t).le
  have htail := transferTailPathWeight_flip_cross
    FieldGhostDict.flipV A a ha0 hA0
      (rectangularPrismTransferBoundaryVector_flip_cross hbeta n)
      (rectangularPrismTransfer_flip_cross hbeta n) k q r
  have hend := oddPrismLayerHalfWeight_flip_cross hbeta n
    (q (Fin.last k)) (r (Fin.last k))
  have htail0 (p : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= transferTailPathWeight A a k p := by
    unfold transferTailPathWeight
    exact mul_nonneg (ha0 _) (Finset.prod_nonneg fun j _ => hA0 _ _)
  unfold oddPrismUpperSlabPathWeight
  change (transferTailPathWeight A a k (oddPrismFlipLayerPath q) *
      oddPrismLayerHalfWeight beta n
        (oddPrismFlipLayerPath q (Fin.last k))) *
    (transferTailPathWeight A a k r *
      oddPrismLayerHalfWeight beta n (r (Fin.last k))) <= _
  calc
    (transferTailPathWeight A a k (oddPrismFlipLayerPath q) *
          oddPrismLayerHalfWeight beta n
            (oddPrismFlipLayerPath q (Fin.last k))) *
        (transferTailPathWeight A a k r *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) =
      (transferTailPathWeight A a k (oddPrismFlipLayerPath q) *
          transferTailPathWeight A a k r) *
        (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (q (Fin.last k))) *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) := by
            simp only [oddPrismFlipLayerPath_apply]
            ring
    _ <=
      (transferTailPathWeight A a k (oddPrismFlipLayerPath (q ⊓ r)) *
          transferTailPathWeight A a k (q ⊔ r)) *
        (oddPrismLayerHalfWeight beta n
            (FieldGhostDict.flipV ((q ⊓ r) (Fin.last k))) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by
      apply mul_le_mul htail
      · simpa only [Pi.inf_apply, Pi.sup_apply] using hend
      · exact mul_nonneg
          (oddPrismLayerHalfWeight_pos beta n _).le
          (oddPrismLayerHalfWeight_pos beta n _).le
      · exact mul_nonneg
          (htail0 (oddPrismFlipLayerPath (q ⊓ r))) (htail0 (q ⊔ r))
    _ =
      (transferTailPathWeight A a k (oddPrismFlipLayerPath (q ⊓ r)) *
          oddPrismLayerHalfWeight beta n
            (oddPrismFlipLayerPath (q ⊓ r) (Fin.last k))) *
        (transferTailPathWeight A a k (q ⊔ r) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by
            simp only [oddPrismFlipLayerPath_apply]
            ring


def oddPrismUpperSlabFlippedEndpointMarginal
    (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  ∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
    oddPrismUpperSlabPathWeight beta n k
      (oddPrismFlipLayerPath (Fin.snoc q s))

theorem oddPrismUpperSlabFlippedEndpointMarginal_eq
    (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabFlippedEndpointMarginal beta n k s =
      oddPrismUpperSlabEndpointMarginal beta n k
        (FieldGhostDict.flipV s) := by
  let e : (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ≃
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :=
    { toFun := oddPrismFlipLayerPath
      invFun := oddPrismFlipLayerPath
      left_inv := oddPrismFlipLayerPath_involutive
      right_inv := oddPrismFlipLayerPath_involutive }
  unfold oddPrismUpperSlabFlippedEndpointMarginal
    oddPrismUpperSlabEndpointMarginal
  calc
    (∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
      oddPrismUpperSlabPathWeight beta n k
        (oddPrismFlipLayerPath (Fin.snoc q s))) =
      ∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
        oddPrismUpperSlabPathWeight beta n k
          (Fin.snoc (e q) (FieldGhostDict.flipV s)) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [e]
      · simp [e]
    _ = _ := Equiv.sum_comp e
      (fun q => oddPrismUpperSlabPathWeight beta n k
        (Fin.snoc q (FieldGhostDict.flipV s)))



theorem oddPrismUpperSlabEndpointMarginal_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabFlippedEndpointMarginal beta n k s *
        oddPrismUpperSlabEndpointMarginal beta n k t <=
      oddPrismUpperSlabFlippedEndpointMarginal beta n k (s ⊓ t) *
        oddPrismUpperSlabEndpointMarginal beta n k (s ⊔ t) := by
  let Fminus : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) -> Real :=
    fun p => oddPrismUpperSlabPathWeight beta n k
      (oddPrismFlipLayerPath (Fin.snoc p.2 p.1))
  let Fplus : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) -> Real :=
    fun p => oddPrismUpperSlabPathWeight beta n k (Fin.snoc p.2 p.1)
  have hminus : 0 <= Fminus := by
    intro p
    unfold Fminus oddPrismUpperSlabPathWeight transferTailPathWeight
    exact mul_nonneg
      (mul_nonneg
        (rectangularPrismTransferBoundaryVector_pos
          1 beta (2 * n + 1) (2 * n + 1) _).le
        (Finset.prod_nonneg fun j _ =>
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) _ _).le))
      (oddPrismLayerHalfWeight_pos beta n _).le
  have hplus : 0 <= Fplus := by
    intro p
    unfold Fplus oddPrismUpperSlabPathWeight transferTailPathWeight
    exact mul_nonneg
      (mul_nonneg
        (rectangularPrismTransferBoundaryVector_pos
          1 beta (2 * n + 1) (2 * n + 1) _).le
        (Finset.prod_nonneg fun j _ =>
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) _ _).le))
      (oddPrismLayerHalfWeight_pos beta n _).le
  have hcross : ∀ x y,
      Fminus x * Fplus y <= Fminus (x ⊓ y) * Fplus (x ⊔ y) := by
    intro x y
    obtain ⟨s, q⟩ := x
    obtain ⟨t, r⟩ := y
    have hpath := oddPrismUpperSlabPathWeight_flip_cross
      hbeta n k (Fin.snoc q s) (Fin.snoc r t)
    have hinf : Fin.snoc q s ⊓ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊓ r) (s ⊓ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    have hsup : Fin.snoc q s ⊔ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊔ r) (s ⊔ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [hinf, hsup] at hpath
    exact hpath
  exact finiteCrossMarginal Fminus Fplus hminus hplus hcross s t


theorem oddPrismUpperConditionedVector_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV s) *
        oddPrismUpperConditionedVector beta n t <=
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (s ⊓ t)) *
        oddPrismUpperConditionedVector beta n (s ⊔ t) := by
  rw [← oddPrismUpperSlabEndpointMarginal_eq_conditioned beta n]
  rw [← oddPrismUpperSlabFlippedEndpointMarginal_eq beta n (n - 1) s,
    ← oddPrismUpperSlabFlippedEndpointMarginal_eq beta n (n - 1) (s ⊓ t)]
  exact oddPrismUpperSlabEndpointMarginal_flip_cross hbeta n (n - 1) s t


def oddPrismTransferFlippedTiltedPairWeight
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  oddPrismLowerConditionedVector beta n x.1 *
    oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV x.2) *
    oddPrismPureSeamKernel r n x.1 x.2

theorem oddPrismTransferFlippedTiltedPairWeight_pos
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismTransferFlippedTiltedPairWeight beta n r x := by
  unfold oddPrismTransferFlippedTiltedPairWeight
  exact mul_pos (mul_pos
    (oddPrismLowerConditionedVector_pos beta n x.1)
    (oddPrismUpperConditionedVector_pos beta n (FieldGhostDict.flipV x.2)))
    (oddPrismPureSeamKernel_pos r n x.1 x.2)



theorem oddPrismTransferTiltedPairWeight_flip_cross
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferTiltedPairWeight beta n r y <=
      oddPrismTransferFlippedTiltedPairWeight beta n r (x ⊓ y) *
        oddPrismTransferTiltedPairWeight beta n r (x ⊔ y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hl := oddPrismLowerConditionedVector_logSupermodular
    hbeta n hn s t
  have hu := oddPrismUpperConditionedVector_flip_cross hbeta n v w
  have hk := oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w
  have hl0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLowerConditionedVector beta n a :=
    (oddPrismLowerConditionedVector_pos beta n a).le
  have hu0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismUpperConditionedVector beta n a :=
    (oddPrismUpperConditionedVector_pos beta n a).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel r n a b :=
    (oddPrismPureSeamKernel_pos r n a b).le
  unfold oddPrismTransferFlippedTiltedPairWeight
    oddPrismTransferTiltedPairWeight oddPrismTransferPairBaseWeight
  calc
    (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV v) *
          oddPrismPureSeamKernel r n s v) *
        (oddPrismLowerConditionedVector beta n t *
          oddPrismUpperConditionedVector beta n w *
          oddPrismPureSeamKernel r n t w) =
      (oddPrismLowerConditionedVector beta n s *
          oddPrismLowerConditionedVector beta n t) *
        (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV v) *
          oddPrismUpperConditionedVector beta n w) *
        (oddPrismPureSeamKernel r n s v *
          oddPrismPureSeamKernel r n t w) := by ring
    _ <=
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismLowerConditionedVector beta n (s ⊔ t)) *
        (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) *
        (oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by
      have hk' : oddPrismPureSeamKernel r n s v *
            oddPrismPureSeamKernel r n t w <=
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
            oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) := by
        simpa only [mul_comm] using hk
      have hLU :
          (oddPrismLowerConditionedVector beta n s *
              oddPrismLowerConditionedVector beta n t) *
            (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV v) *
              oddPrismUpperConditionedVector beta n w) <=
          (oddPrismLowerConditionedVector beta n (s ⊓ t) *
              oddPrismLowerConditionedVector beta n (s ⊔ t)) *
            (oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (v ⊓ w)) *
              oddPrismUpperConditionedVector beta n (v ⊔ w)) := by
        apply mul_le_mul hl hu
        · exact mul_nonneg (hu0 (FieldGhostDict.flipV v)) (hu0 w)
        · exact mul_nonneg (hl0 (s ⊓ t)) (hl0 (s ⊔ t))
      apply mul_le_mul hLU hk'
      · exact mul_nonneg (hk0 s v) (hk0 t w)
      · exact mul_nonneg
          (mul_nonneg (hl0 (s ⊓ t)) (hl0 (s ⊔ t)))
          (mul_nonneg (hu0 (FieldGhostDict.flipV (v ⊓ w))) (hu0 (v ⊔ w)))
    _ =
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w)) *
        (oddPrismLowerConditionedVector beta n (s ⊔ t) *
          oddPrismUpperConditionedVector beta n (v ⊔ w) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by ring

theorem oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeFlippedRawMoment beta n r =
      ∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x := by
  unfold oddPrismTransferBridgeFlippedRawMoment
    oddPrismTransferFlippedTiltedPairWeight
  rw [Fintype.sum_prod_type]

def oddPrismTransferTiltedPairProb
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  oddPrismTransferTiltedPairWeight beta n r x /
    oddPrismTransferBridgeRawMoment beta n r

def oddPrismTransferFlippedTiltedPairProb
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  oddPrismTransferFlippedTiltedPairWeight beta n r x /
    oddPrismTransferBridgeFlippedRawMoment beta n r

theorem oddPrismTransferBridgeFlippedRawMoment_pos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 < oddPrismTransferBridgeFlippedRawMoment beta n r := by
  rw [← oddPrismTransferBridgeRawMoment_neg_eq_flipped]
  exact oddPrismTransferBridgeRawMoment_pos beta n hn (-r)

theorem sum_oddPrismTransferTiltedPairProb
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ x, oddPrismTransferTiltedPairProb beta n r x) = 1 := by
  unfold oddPrismTransferTiltedPairProb
  rw [← Finset.sum_div,
    ← oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight]
  exact div_self (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'

theorem sum_oddPrismTransferFlippedTiltedPairProb
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x) = 1 := by
  unfold oddPrismTransferFlippedTiltedPairProb
  rw [← Finset.sum_div,
    ← oddPrismTransferBridgeFlippedRawMoment_eq_sum_pairWeight]
  exact div_self (oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r).ne'

theorem oddPrismTransferTiltedPairProb_nonneg
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 <= oddPrismTransferTiltedPairProb beta n r := by
  intro x
  exact div_nonneg (oddPrismTransferTiltedPairWeight_pos beta n r x).le
    (oddPrismTransferBridgeRawMoment_pos beta n hn r).le

theorem oddPrismTransferFlippedTiltedPairProb_nonneg
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    0 <= oddPrismTransferFlippedTiltedPairProb beta n r := by
  intro x
  exact div_nonneg (oddPrismTransferFlippedTiltedPairWeight_pos beta n r x).le
    (oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r).le

theorem oddPrismTransferTiltedPairProb_flip_cross
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferFlippedTiltedPairProb beta n r x *
        oddPrismTransferTiltedPairProb beta n r y <=
      oddPrismTransferFlippedTiltedPairProb beta n r (x ⊓ y) *
        oddPrismTransferTiltedPairProb beta n r (x ⊔ y) := by
  have hraw := oddPrismTransferTiltedPairWeight_flip_cross
    hbeta hr n hn x y
  unfold oddPrismTransferFlippedTiltedPairProb
    oddPrismTransferTiltedPairProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos
    (oddPrismTransferBridgeFlippedRawMoment_pos beta n hn r)
    (oddPrismTransferBridgeRawMoment_pos beta n hn r))).mpr hraw



theorem oddPrismTransferFlippedTiltedPair_le_of_monotone
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    {g : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real}
    (hg : Monotone g) (hg0 : 0 <= g) :
    (∑ x, g x * oddPrismTransferFlippedTiltedPairProb beta n r x) <=
      ∑ x, g x * oddPrismTransferTiltedPairProb beta n r x := by
  apply holley
  · exact hg0
  · exact oddPrismTransferFlippedTiltedPairProb_nonneg beta n hn r
  · exact oddPrismTransferTiltedPairProb_nonneg beta n hn r
  · exact hg
  · rw [sum_oddPrismTransferFlippedTiltedPairProb beta n hn r,
      sum_oddPrismTransferTiltedPairProb beta n hn r]
  · exact oddPrismTransferTiltedPairProb_flip_cross hbeta hr n hn

theorem oddPrismTransferTiltedPairProb_mean
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x) =
      oddPrismTransferBridgeRawFirst beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) =
        oddPrismTransferBridgeRawFirst beta n r := by
    unfold oddPrismTransferTiltedPairWeight oddPrismTransferPairBaseWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeRawFirst
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferTiltedPairProb
  rw [show (∑ x, oddPrismTransferTiltedPairWeight beta n r x /
      oddPrismTransferBridgeRawMoment beta n r *
        oddPrismTransferPairInteraction n x) =
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) /
          oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferTiltedPairProb_second
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x ^ 2) =
      oddPrismTransferBridgeRawSecond beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) =
        oddPrismTransferBridgeRawSecond beta n r := by
    unfold oddPrismTransferTiltedPairWeight oddPrismTransferPairBaseWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeRawSecond
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferTiltedPairProb
  rw [show (∑ x, oddPrismTransferTiltedPairWeight beta n r x /
      oddPrismTransferBridgeRawMoment beta n r *
        oddPrismTransferPairInteraction n x ^ 2) =
      (∑ x, oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) /
          oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferBridgeVariance_eq_pairProbVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      (∑ x, oddPrismTransferTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) -
      (∑ x, oddPrismTransferTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x) ^ 2 := by
  rw [oddPrismTransferTiltedPairProb_mean,
    oddPrismTransferTiltedPairProb_second]
  rfl

theorem oddPrismTransferFlippedTiltedPairProb_mean
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x) =
      oddPrismTransferBridgeFlippedRawFirst beta n r /
        oddPrismTransferBridgeFlippedRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) =
        oddPrismTransferBridgeFlippedRawFirst beta n r := by
    unfold oddPrismTransferFlippedTiltedPairWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeFlippedRawFirst
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferFlippedTiltedPairProb
  rw [show (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x /
      oddPrismTransferBridgeFlippedRawMoment beta n r *
        oddPrismTransferPairInteraction n x) =
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x) /
          oddPrismTransferBridgeFlippedRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferFlippedTiltedPairProb_second
    (beta : Real) (n : Nat) (r : Real) :
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x ^ 2) =
      oddPrismTransferBridgeFlippedRawSecond beta n r /
        oddPrismTransferBridgeFlippedRawMoment beta n r := by
  have hnum :
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) =
        oddPrismTransferBridgeFlippedRawSecond beta n r := by
    unfold oddPrismTransferFlippedTiltedPairWeight
      oddPrismTransferPairInteraction oddPrismTransferBridgeFlippedRawSecond
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold oddPrismTransferFlippedTiltedPairProb
  rw [show (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x /
      oddPrismTransferBridgeFlippedRawMoment beta n r *
        oddPrismTransferPairInteraction n x ^ 2) =
      (∑ x, oddPrismTransferFlippedTiltedPairWeight beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) /
          oddPrismTransferBridgeFlippedRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hnum]

theorem oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeFlippedVariance beta n r =
      (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x ^ 2) -
      (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
        oddPrismTransferPairInteraction n x) ^ 2 := by
  rw [oddPrismTransferFlippedTiltedPairProb_mean,
    oddPrismTransferFlippedTiltedPairProb_second]
  rfl



theorem oddPrismTransferBridgeVariance_le_neg_iff_pairProbVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r <=
        oddPrismTransferBridgeVariance beta n (-r) ↔
      (∑ x, oddPrismTransferTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x ^ 2) -
        (∑ x, oddPrismTransferTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x) ^ 2 <=
      (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x ^ 2) -
        (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
          oddPrismTransferPairInteraction n x) ^ 2 := by
  rw [oddPrismTransferBridgeVariance_neg_eq_flipped,
    oddPrismTransferBridgeVariance_eq_pairProbVariance,
    oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance]


def oddPrismTransferPairAgreementSpin (n : Nat)
    (p : Fin (2 * n + 1) × Fin (2 * n + 1))
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) : Real :=
  spin x.1 p * spin x.2 p

theorem oddPrismTransferPairInteraction_eq_sum_agreementSpin
    (n : Nat)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferPairInteraction n x =
      ∑ p, oddPrismTransferPairAgreementSpin n p x := by
  rfl



def oddPrismTransferTiltedPairCovarianceRow
    (beta : Real) (n : Nat) (r : Real)
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) : Real :=
  (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      (oddPrismTransferPairAgreementSpin n p x *
        oddPrismTransferPairInteraction n x)) -
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairAgreementSpin n p x) *
    (∑ x, oddPrismTransferTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x)


def oddPrismTransferFlippedTiltedPairCovarianceRow
    (beta : Real) (n : Nat) (r : Real)
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) : Real :=
  (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      (oddPrismTransferPairAgreementSpin n p x *
        oddPrismTransferPairInteraction n x)) -
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairAgreementSpin n p x) *
    (∑ x, oddPrismTransferFlippedTiltedPairProb beta n r x *
      oddPrismTransferPairInteraction n x)

theorem oddPrismTransferBridgeVariance_eq_sum_covarianceRows
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      ∑ p, oddPrismTransferTiltedPairCovarianceRow beta n r p := by
  rw [oddPrismTransferBridgeVariance_eq_pairProbVariance]
  unfold oddPrismTransferTiltedPairCovarianceRow
    oddPrismTransferPairAgreementSpin
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    ring
  · rw [← Finset.sum_mul]
    rw [pow_two]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    rw [Finset.mul_sum]

theorem oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeFlippedVariance beta n r =
      ∑ p, oddPrismTransferFlippedTiltedPairCovarianceRow beta n r p := by
  rw [oddPrismTransferBridgeFlippedVariance_eq_pairProbVariance]
  unfold oddPrismTransferFlippedTiltedPairCovarianceRow
    oddPrismTransferPairAgreementSpin
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    ring
  · rw [← Finset.sum_mul]
    rw [pow_two]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    unfold oddPrismTransferPairInteraction oddPrismLayerSeamInteraction
    rw [Finset.mul_sum]



theorem oddPrismTransferBridgeVariance_le_neg_of_covarianceRows
    (beta : Real) (n : Nat) (r : Real)
    (hrow : ∀ p,
      oddPrismTransferTiltedPairCovarianceRow beta n r p <=
        oddPrismTransferFlippedTiltedPairCovarianceRow beta n r p) :
    oddPrismTransferBridgeVariance beta n r <=
      oddPrismTransferBridgeVariance beta n (-r) := by
  rw [oddPrismTransferBridgeVariance_neg_eq_flipped,
    oddPrismTransferBridgeVariance_eq_sum_covarianceRows,
    oddPrismTransferBridgeFlippedVariance_eq_sum_covarianceRows]
  exact Finset.sum_le_sum fun p _ => hrow p





def oddPrismTransferAgreementFibreMass
    (beta : Real) (n : Nat)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) : Real :=
  ∑ s, oddPrismLowerConditionedVector beta n s *
    oddPrismUpperConditionedVector beta n (ghsLMate q s)



def oddPrismTransferAgreementSpin (n : Nat)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) : Real :=
  ∑ p, spin q p

theorem spin_ghsLAgreement
    {V : Type*} (s t : ConfigSpace V) (p : V) :
    spin (ghsLAgreement s t) p = spin s p * spin t p := by
  unfold ghsLAgreement spin
  cases hs : s p <;> cases ht : t p <;> norm_num [hs, ht]

theorem oddPrismLayerSeamInteraction_eq_agreementSpin
    (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s t =
      oddPrismTransferAgreementSpin n (ghsLAgreement s t) := by
  unfold oddPrismLayerSeamInteraction oddPrismTransferAgreementSpin
  apply Finset.sum_congr rfl
  intro p _
  rw [spin_ghsLAgreement]

@[simp] theorem oddPrismLayerSeamInteraction_mate
    (n : Nat)
    (q s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s (ghsLMate q s) =
      oddPrismTransferAgreementSpin n q := by
  rw [oddPrismLayerSeamInteraction_eq_agreementSpin,
    ghsLAgreement_mate]

theorem oddPrismTransferAgreementFibreMass_pos
    (beta : Real) (n : Nat)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 < oddPrismTransferAgreementFibreMass beta n q := by
  unfold oddPrismTransferAgreementFibreMass
  exact Finset.sum_pos (fun s _ => mul_pos
    (oddPrismLowerConditionedVector_pos beta n s)
    (oddPrismUpperConditionedVector_pos beta n (ghsLMate q s)))
    Finset.univ_nonempty


theorem oddPrismTransferBridgeRawMoment_eq_agreementTilt
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ q, oddPrismTransferAgreementFibreMass beta n q *
        Real.exp (r * oddPrismTransferAgreementSpin n q) := by
  unfold oddPrismTransferBridgeRawMoment
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferAgreementFibreMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_mate]

theorem oddPrismTransferBridgeRawFirst_eq_agreementTilt
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawFirst beta n r =
      ∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q *
          Real.exp (r * oddPrismTransferAgreementSpin n q)) := by
  unfold oddPrismTransferBridgeRawFirst
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferAgreementFibreMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_mate]

theorem oddPrismTransferBridgeRawSecond_eq_agreementTilt
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawSecond beta n r =
      ∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q ^ 2 *
          Real.exp (r * oddPrismTransferAgreementSpin n q)) := by
  unfold oddPrismTransferBridgeRawSecond
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferAgreementFibreMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_mate]


def oddPrismTransferAgreementTiltProb
    (beta : Real) (n : Nat) (r : Real)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) : Real :=
  oddPrismTransferAgreementFibreMass beta n q *
      Real.exp (r * oddPrismTransferAgreementSpin n q) /
    oddPrismTransferBridgeRawMoment beta n r

theorem oddPrismTransferAgreementTiltProb_pos
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 < oddPrismTransferAgreementTiltProb beta n r q := by
  unfold oddPrismTransferAgreementTiltProb
  exact div_pos (mul_pos
    (oddPrismTransferAgreementFibreMass_pos beta n q) (Real.exp_pos _))
    (oddPrismTransferBridgeRawMoment_pos beta n hn r)

theorem sum_oddPrismTransferAgreementTiltProb
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ q, oddPrismTransferAgreementTiltProb beta n r q) = 1 := by
  unfold oddPrismTransferAgreementTiltProb
  rw [← Finset.sum_div,
    ← oddPrismTransferBridgeRawMoment_eq_agreementTilt]
  exact div_self (oddPrismTransferBridgeRawMoment_pos beta n hn r).ne'

theorem oddPrismTransferAgreementSpin_monotone (n : Nat) :
    Monotone (oddPrismTransferAgreementSpin n) := by
  intro q s hqs
  unfold oddPrismTransferAgreementSpin
  exact Finset.sum_le_sum fun p _ => ifk_spin_mono hqs p

theorem oddPrismTransferAgreementTiltProb_mean
    (beta : Real) (n : Nat) (r : Real) :
    (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
      oddPrismTransferAgreementSpin n q) =
      oddPrismTransferBridgeRawFirst beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  unfold oddPrismTransferAgreementTiltProb
  rw [show (∑ q, (oddPrismTransferAgreementFibreMass beta n q *
        Real.exp (r * oddPrismTransferAgreementSpin n q) /
          oddPrismTransferBridgeRawMoment beta n r) *
        oddPrismTransferAgreementSpin n q) =
      (∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q *
          Real.exp (r * oddPrismTransferAgreementSpin n q))) /
        oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    ring]
  rw [← oddPrismTransferBridgeRawFirst_eq_agreementTilt]

theorem oddPrismTransferAgreementTiltProb_second
    (beta : Real) (n : Nat) (r : Real) :
    (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
      oddPrismTransferAgreementSpin n q ^ 2) =
      oddPrismTransferBridgeRawSecond beta n r /
        oddPrismTransferBridgeRawMoment beta n r := by
  unfold oddPrismTransferAgreementTiltProb
  rw [show (∑ q, (oddPrismTransferAgreementFibreMass beta n q *
        Real.exp (r * oddPrismTransferAgreementSpin n q) /
          oddPrismTransferBridgeRawMoment beta n r) *
        oddPrismTransferAgreementSpin n q ^ 2) =
      (∑ q, oddPrismTransferAgreementFibreMass beta n q *
        (oddPrismTransferAgreementSpin n q ^ 2 *
          Real.exp (r * oddPrismTransferAgreementSpin n q))) /
        oddPrismTransferBridgeRawMoment beta n r by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    ring]
  rw [← oddPrismTransferBridgeRawSecond_eq_agreementTilt]

theorem oddPrismTransferBridgeVariance_eq_agreementVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r =
      (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
        oddPrismTransferAgreementSpin n q ^ 2) -
      (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
        oddPrismTransferAgreementSpin n q) ^ 2 := by
  rw [oddPrismTransferAgreementTiltProb_mean,
    oddPrismTransferAgreementTiltProb_second]
  rfl



theorem oddPrismTransferBridgeVariance_le_neg_iff_agreementVariance
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVariance beta n r <=
        oddPrismTransferBridgeVariance beta n (-r) ↔
      (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
          oddPrismTransferAgreementSpin n q ^ 2) -
        (∑ q, oddPrismTransferAgreementTiltProb beta n r q *
          oddPrismTransferAgreementSpin n q) ^ 2 <=
      (∑ q, oddPrismTransferAgreementTiltProb beta n (-r) q *
          oddPrismTransferAgreementSpin n q ^ 2) -
        (∑ q, oddPrismTransferAgreementTiltProb beta n (-r) q *
          oddPrismTransferAgreementSpin n q) ^ 2 := by
  rw [oddPrismTransferBridgeVariance_eq_agreementVariance,
    oddPrismTransferBridgeVariance_eq_agreementVariance]



def ghsLMateEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (s : ConfigSpace V) :
    ConfigSpace V ≃ ConfigSpace V where
  toFun q := ghsLMate q s
  invFun t := ghsLAgreement s t
  left_inv q := ghsLAgreement_mate q s
  right_inv t := ghsLMate_agreement s t

@[simp] theorem ghsLMateEquiv_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (s q : ConfigSpace V) :
    ghsLMateEquiv s q = ghsLMate q s := rfl



theorem ghsLAgreement_chain
    {V : Type*} (s t v : ConfigSpace V) :
    ghsLAgreement (ghsLAgreement s t) (ghsLAgreement t v) =
      ghsLAgreement s v := by
  funext p
  unfold ghsLAgreement
  cases hs : s p <;> cases ht : t p <;> cases hv : v p <;>
    simp [hs, ht, hv]




theorem oddPrismLayerSeamInteraction_mate_signed
    (n : Nat)
    (c s t : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismLayerSeamInteraction n s (ghsLMate c t) =
      ∑ p, spin c p * (spin s p * spin t p) := by
  unfold oddPrismLayerSeamInteraction ghsLMate spin
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : c p <;> cases hs : s p <;> cases ht : t p <;>
    simp [hc, hs, ht]



theorem oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling
    (n : Nat) (a b : Real)
    (c s t : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    a * oddPrismLayerSeamInteraction n s (ghsLMate c t) +
        b * oddPrismLayerSeamInteraction n s t =
      ∑ p, (b + a * spin c p) * (spin s p * spin t p) := by
  rw [oddPrismLayerSeamInteraction_mate_signed]
  unfold oddPrismLayerSeamInteraction
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem oddPrism_endpointAgreementCoupling_nonneg
    {beta r : Real} (hr : 0 <= r) (hrb : r <= beta)
    {n : Nat}
    (c : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)))
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) :
    0 <= beta + r * spin c p := by
  rcases spin_eq_pm c p with hp | hp
  · rw [hp, mul_one]
    linarith
  · rw [hp, mul_neg_one]
    linarith




def oddPrismEndpointAgreementThreeLayerRawMoment
    (beta : Real) (n : Nat) (a b : Real) : Real :=
  ∑ c, ∑ t, ∑ s,
    oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperConditionedVector beta n (ghsLMate c t) *
      oddPrismUpperConditionedVector beta n t *
      Real.exp (∑ p, (b + a * spin c p) * (spin s p * spin t p))

theorem oddPrismThreeLayerRawMoment_eq_endpointAgreement
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b =
      oddPrismEndpointAgreementThreeLayerRawMoment beta n a b := by
  unfold oddPrismThreeLayerRawMoment
    oddPrismEndpointAgreementThreeLayerRawMoment
  calc
    (∑ s, ∑ v, ∑ t,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s v *
          oddPrismPureSeamKernel b n s t) =
      ∑ s, ∑ t, ∑ v,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s v *
          oddPrismPureSeamKernel b n s t := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.sum_comm]
    _ = ∑ s, ∑ t, ∑ c,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate c t) *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s (ghsLMate c t) *
          oddPrismPureSeamKernel b n s t := by
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro t _
            rw [← Equiv.sum_comp (ghsLMateEquiv t)]
            rfl
    _ = ∑ c, ∑ t, ∑ s,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate c t) *
          oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel a n s (ghsLMate c t) *
          oddPrismPureSeamKernel b n s t := by
            rw [show (∑ s, ∑ t, ∑ c,
                oddPrismLayerHalfWeight beta n s ^ 2 *
                  oddPrismUpperConditionedVector beta n (ghsLMate c t) *
                  oddPrismUpperConditionedVector beta n t *
                  oddPrismPureSeamKernel a n s (ghsLMate c t) *
                  oddPrismPureSeamKernel b n s t) =
              ∑ s, ∑ c, ∑ t,
                oddPrismLayerHalfWeight beta n s ^ 2 *
                  oddPrismUpperConditionedVector beta n (ghsLMate c t) *
                  oddPrismUpperConditionedVector beta n t *
                  oddPrismPureSeamKernel a n s (ghsLMate c t) *
                  oddPrismPureSeamKernel b n s t by
                    apply Finset.sum_congr rfl
                    intro s _
                    rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      unfold oddPrismPureSeamKernel
      let C := oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismUpperConditionedVector beta n (ghsLMate c t) *
        oddPrismUpperConditionedVector beta n t
      rw [show oddPrismLayerHalfWeight beta n s ^ 2 *
            oddPrismUpperConditionedVector beta n (ghsLMate c t) *
            oddPrismUpperConditionedVector beta n t *
            Real.exp (a * oddPrismLayerSeamInteraction n s (ghsLMate c t)) *
            Real.exp (b * oddPrismLayerSeamInteraction n s t) =
          C * (Real.exp (a * oddPrismLayerSeamInteraction n s (ghsLMate c t)) *
            Real.exp (b * oddPrismLayerSeamInteraction n s t)) by
              unfold C
              ring,
        ← Real.exp_add,
        oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling]


def oddPrismThreeLayerEndpointSum
    (beta : Real) (n : Nat) (a : Real)
    (s : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) : Real :=
  ∑ v, oddPrismUpperConditionedVector beta n v *
    oddPrismPureSeamKernel a n s v



theorem oddPrismThreeLayerRawMoment_eq_gram
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b =
      ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n a s *
        oddPrismThreeLayerEndpointSum beta n b s := by
  unfold oddPrismThreeLayerRawMoment oddPrismThreeLayerEndpointSum
  apply Finset.sum_congr rfl
  intro s _
  rw [show oddPrismLayerHalfWeight beta n s ^ 2 *
        (∑ v, oddPrismUpperConditionedVector beta n v *
          oddPrismPureSeamKernel a n s v) *
        (∑ t, oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel b n s t) =
      (∑ v, oddPrismLayerHalfWeight beta n s ^ 2 *
        (oddPrismUpperConditionedVector beta n v *
          oddPrismPureSeamKernel a n s v)) *
        ∑ t, oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel b n s t by
            rw [← Finset.mul_sum]]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro t _
  ring


theorem oddPrismThreeLayerRawMoment_sq_le_diagonal
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b ^ 2 <=
      oddPrismThreeLayerRawMoment beta n a a *
        oddPrismThreeLayerRawMoment beta n b b := by
  rw [oddPrismThreeLayerRawMoment_eq_gram,
    oddPrismThreeLayerRawMoment_eq_gram,
    oddPrismThreeLayerRawMoment_eq_gram]
  let f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
    fun s => oddPrismLayerHalfWeight beta n s *
      oddPrismThreeLayerEndpointSum beta n a s
  let g : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
    fun s => oddPrismLayerHalfWeight beta n s *
      oddPrismThreeLayerEndpointSum beta n b s
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset
      (ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)))) f g
  have hab : (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n a s *
        oddPrismThreeLayerEndpointSum beta n b s) =
      ∑ s, f s * g s := by
    apply Finset.sum_congr rfl
    intro s _
    unfold f g
    ring
  have haa : (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n a s *
        oddPrismThreeLayerEndpointSum beta n a s) =
      ∑ s, f s ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    unfold f
    ring
  have hbb : (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n b s *
        oddPrismThreeLayerEndpointSum beta n b s) =
      ∑ s, g s ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    unfold g
    ring
  rw [hab, haa, hbb]
  exact hcs



def oddPrismAgreementEndpointKernel
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) : Real :=
  ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
    oddPrismUpperConditionedVector beta n (ghsLMate a s) *
    oddPrismUpperConditionedVector beta n (ghsLMate q s)

theorem oddPrismAgreementEndpointKernel_pos
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 < oddPrismAgreementEndpointKernel beta n a q := by
  unfold oddPrismAgreementEndpointKernel
  apply Finset.sum_pos
  · intro s _
    exact mul_pos
      (mul_pos (sq_pos_of_pos (oddPrismLayerHalfWeight_pos beta n s))
        (oddPrismUpperConditionedVector_pos beta n (ghsLMate a s)))
      (oddPrismUpperConditionedVector_pos beta n (ghsLMate q s))
  · exact Finset.univ_nonempty

theorem oddPrismAgreementEndpointKernel_symm
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismAgreementEndpointKernel beta n a q =
      oddPrismAgreementEndpointKernel beta n q a := by
  unfold oddPrismAgreementEndpointKernel
  apply Finset.sum_congr rfl
  intro s _
  ring




theorem oddPrismAgreementEndpointKernel_quadratic_eq
    (beta : Real) (n : Nat)
    (f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real) :
    (∑ a, ∑ q, f a * oddPrismAgreementEndpointKernel beta n a q * f q) =
      ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        (∑ a, f a * oddPrismUpperConditionedVector beta n (ghsLMate a s)) ^ 2 := by
  unfold oddPrismAgreementEndpointKernel
  calc
    (∑ a, ∑ q, f a *
        (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q) =
      ∑ a, ∑ q, ∑ s, f a *
        (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ s, ∑ q, f a *
        (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
    _ = ∑ s, ∑ a, ∑ q, f a *
        (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      let g : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
        fun a => f a *
          oddPrismUpperConditionedVector beta n (ghsLMate a s)
      calc
        (∑ a, ∑ q, f a *
            (oddPrismLayerHalfWeight beta n s ^ 2 *
              oddPrismUpperConditionedVector beta n (ghsLMate a s) *
              oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q) =
          ∑ a, ∑ q,
            (oddPrismLayerHalfWeight beta n s ^ 2 * g a) * g q := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro q _
              unfold g
              ring
        _ = (∑ a, oddPrismLayerHalfWeight beta n s ^ 2 * g a) *
            ∑ q, g q := by
              rw [Fintype.sum_mul_sum]
        _ = oddPrismLayerHalfWeight beta n s ^ 2 * (∑ a, g a) ^ 2 := by
              rw [← Finset.mul_sum]
              ring
        _ = _ := by rfl

theorem oddPrismAgreementEndpointKernel_quadratic_nonneg
    (beta : Real) (n : Nat)
    (f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real) :
    0 <= ∑ a, ∑ q,
      f a * oddPrismAgreementEndpointKernel beta n a q * f q := by
  rw [oddPrismAgreementEndpointKernel_quadratic_eq]
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)




theorem oddPrismTransferAgreementFibreMass_eq_kernelTilt
    (beta : Real) (n : Nat) (hn : 0 < n)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismTransferAgreementFibreMass beta n q =
      ∑ a, oddPrismAgreementEndpointKernel beta n a q *
        Real.exp (beta * oddPrismTransferAgreementSpin n a) := by
  unfold oddPrismTransferAgreementFibreMass
  calc
    (∑ s, oddPrismLowerConditionedVector beta n s *
        oddPrismUpperConditionedVector beta n (ghsLMate q s)) =
      ∑ s, (oddPrismLayerHalfWeight beta n s ^ 2 *
          ∑ v, oddPrismPureSeamKernel beta n s v *
            oddPrismUpperConditionedVector beta n v) *
        oddPrismUpperConditionedVector beta n (ghsLMate q s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s]
    _ = ∑ s, ∑ a,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s) *
          Real.exp (beta * oddPrismTransferAgreementSpin n a) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Equiv.sum_comp (ghsLMateEquiv s)]
      simp only [ghsLMateEquiv_apply]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      unfold oddPrismPureSeamKernel
      rw [oddPrismLayerSeamInteraction_mate]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      unfold oddPrismAgreementEndpointKernel
      rw [Finset.sum_mul]




theorem unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (r : Real) (hr : 0 <= r)
    (hvar : forall t, 0 <= t -> t <= r ->
      unequalReplicaBridgeVariance G H K J hf hg t <=
        unequalReplicaBridgeVariance G H K J hf hg (-t)) :
    unequalReplicaBridgeFreeEnergy G H K J hf hg r <=
      2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean G H K J hf hg t +
      unequalReplicaBridgeMean G H K J hf hg (-t)
  have hdiffD : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      G H K J hf hg t).differentiableAt
  have hanti : AntitoneOn D (Set.Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) r)
    · exact hdiffD.continuous.continuousOn
    · intro t _
      exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).deriv]
      exact sub_nonpos.mpr (hvar t ht.1.le ht.2.le)
  have hmean : forall t, 0 <= t -> t <= r -> D t <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    intro t ht htr
    have hle := hanti (by exact ⟨le_rfl, hr⟩) ⟨ht, htr⟩ ht
    dsimp only [D] at hle
    rw [neg_zero] at hle
    linarith
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [unequalReplicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg t).differentiableAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (unequalReplicaBridgeFreeEnergy G H K J hf hg) hrpos
    hdiffAll.continuous.continuousOn hdiffAll.differentiableOn
  have hderiv : deriv
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) c <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    rw [(hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg c).deriv]
    exact hmean c hc.1.le hc.2.le
  have hzero : unequalReplicaBridgeFreeEnergy G H K J hf hg 0 = 0 := by
    simp [unequalReplicaBridgeFreeEnergy]
  have hmul := mul_le_mul_of_nonneg_right hderiv hrpos.le
  rw [hslope, hzero] at hmul
  simp only [sub_zero] at hmul
  rw [div_mul_cancel₀ _ hrpos.ne'] at hmul
  convert hmul using 1 <;> ring




theorem oddPrismUnequalBridgeFreeEnergy_le_of_transferVarianceOrder_Icc
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (hvar : forall t, 0 <= t -> t <= beta ->
      oddPrismTransferBridgeVariance beta n t <=
        oddPrismTransferBridgeVariance beta n (-t)) :
    oddPrismUnequalBridgeFreeEnergy beta n <=
      2 * beta * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  change unequalReplicaBridgeFreeEnergy
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta
      (fun v => beta * oddPrismPlusField n v.1)
      (fun v => beta * oddPrismPlusField n v.1) beta <= _
  apply unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) beta hbeta
  intro t ht htb
  rw [oddPrismUnequalBridgeVariance_eq_transfer beta n hn t,
    oddPrismUnequalBridgeVariance_eq_transfer beta n hn (-t)]
  exact hvar t ht htb


end

end StatMech.FrontierA
