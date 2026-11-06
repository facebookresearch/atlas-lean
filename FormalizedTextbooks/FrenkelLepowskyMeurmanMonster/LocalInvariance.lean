/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Bilinear bridges for the concrete Conway product and local-action invariance.
-/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalForm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct

-- Expanding the nested finite-coordinate maps requires additional elaboration recursion depth.
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000 in
-- The nested coordinate bilinear expressions exceed the default elaboration heartbeat budget.
theorem conwayRawProduct_add_left (x y z : ConwayRawSpace) :
    conwayRawProduct (x + y) z = conwayRawProduct x z + conwayRawProduct y z := by
  apply Prod.ext
  · funext i j
    change (conwayRawProduct (x + y) z).1 i j =
      (conwayRawProduct x z).1 i j + (conwayRawProduct y z).1 i j
    simp only [conwayRawProduct, Prod.fst_add, Prod.snd_add, Matrix.add_apply,
      Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    simp_rw [ite_add_zero, Finset.sum_add_distrib]
    ring
  · apply Prod.ext
    · funext u
      change (conwayRawProduct (x + y) z).2.1 u =
        (conwayRawProduct x z).2.1 u + (conwayRawProduct y z).2.1 u
      simp only [conwayRawProduct, Prod.fst_add, Prod.snd_add, Matrix.add_apply,
        Pi.add_apply, conwayShortPairing, add_mul, mul_add, Finset.sum_add_distrib,
        spinOperator, LinearMap.coe_mk, AddHom.coe_mk]
      simp_rw [ite_add_zero, Finset.sum_add_distrib]
      ring
    · funext t i
      change (conwayRawProduct (x + y) z).2.2 t i =
        (conwayRawProduct x z).2.2 t i + (conwayRawProduct y z).2.2 t i
      simp only [conwayRawProduct, Prod.fst_add, Prod.snd_add, Matrix.add_apply,
        Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib, Matrix.trace_add,
        spinOperator, LinearMap.coe_mk, AddHom.coe_mk]
      ring

set_option maxHeartbeats 1000000 in
-- The nested coordinate bilinear expressions exceed the default elaboration heartbeat budget.
theorem conwayRawProduct_add_right (x y z : ConwayRawSpace) :
    conwayRawProduct z (x + y) = conwayRawProduct z x + conwayRawProduct z y := by
  apply Prod.ext
  · funext i j
    change (conwayRawProduct z (x + y)).1 i j =
      (conwayRawProduct z x).1 i j + (conwayRawProduct z y).1 i j
    simp only [conwayRawProduct, Prod.fst_add, Prod.snd_add, Matrix.add_apply,
      Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    simp_rw [ite_add_zero, Finset.sum_add_distrib]
    ring
  · apply Prod.ext
    · funext u
      change (conwayRawProduct z (x + y)).2.1 u =
        (conwayRawProduct z x).2.1 u + (conwayRawProduct z y).2.1 u
      simp only [conwayRawProduct, Prod.fst_add, Prod.snd_add, Matrix.add_apply,
        Pi.add_apply, conwayShortPairing, add_mul, mul_add, Finset.sum_add_distrib,
        spinOperator, LinearMap.coe_mk, AddHom.coe_mk]
      simp_rw [ite_add_zero, Finset.sum_add_distrib]
      ring
    · funext t i
      change (conwayRawProduct z (x + y)).2.2 t i =
        (conwayRawProduct z x).2.2 t i + (conwayRawProduct z y).2.2 t i
      simp only [conwayRawProduct, Prod.fst_add, Prod.snd_add, Matrix.add_apply,
        Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib, Matrix.trace_add,
        spinOperator, LinearMap.coe_mk, AddHom.coe_mk]
      ring

theorem spinOperator_smul_pi (q : Q) (c : ℝ) (x : SpinIndex → Fin 24 → ℝ)
    (i : Fin 24) (t : SpinIndex) :
    spinOperator q (fun v => c * x v i) t = c * spinOperator q (fun v => x v i) t := by
  change spinOperator q (c • (fun v => x v i)) t = _
  rw [map_smul]
  rfl

set_option maxHeartbeats 1000000 in
-- The nested coordinate bilinear expressions exceed the default elaboration heartbeat budget.
theorem conwayRawProduct_smul_left (c : ℝ) (x z : ConwayRawSpace) :
    conwayRawProduct (c • x) z = c • conwayRawProduct x z := by
  apply Prod.ext
  · funext i j
    change (conwayRawProduct (c • x) z).1 i j =
      c * (conwayRawProduct x z).1 i j
    simp only [conwayRawProduct, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, add_mul]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    try simp_rw [mul_ite, mul_zero]
    ring_nf
    try simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_ite, mul_zero]
    ring_nf
  · apply Prod.ext
    · funext u
      change (conwayRawProduct (c • x) z).2.1 u =
        c * (conwayRawProduct x z).2.1 u
      simp only [conwayRawProduct, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, conwayShortPairing, mul_add, add_mul,
        spinOperator_smul_pi]
      try simp_rw [Finset.mul_sum, Finset.sum_mul]
      try simp_rw [mul_ite, mul_zero]
      ring_nf
      try simp only [Finset.mul_sum, Finset.sum_mul]
      ring_nf
      simp only [mul_comm, mul_left_comm, mul_assoc]
      ring
    · funext t i
      change (conwayRawProduct (c • x) z).2.2 t i =
        c * (conwayRawProduct x z).2.2 t i
      simp only [conwayRawProduct, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.trace_smul, mul_add, add_mul,
        spinOperator_smul_pi]
      try simp_rw [Finset.mul_sum, Finset.sum_mul]
      try simp_rw [mul_ite, mul_zero]
      ring_nf
      try simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]
      ring_nf
set_option maxHeartbeats 1000000 in
-- The nested coordinate bilinear expressions exceed the default elaboration heartbeat budget.
theorem conwayRawProduct_smul_right (c : ℝ) (x z : ConwayRawSpace) :
    conwayRawProduct z (c • x) = c • conwayRawProduct z x := by
  apply Prod.ext
  · funext i j
    change (conwayRawProduct z (c • x)).1 i j =
      c * (conwayRawProduct z x).1 i j
    simp only [conwayRawProduct, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, add_mul]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    try simp_rw [mul_ite, mul_zero]
    ring_nf
    try simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_ite, mul_zero]
    ring_nf
  · apply Prod.ext
    · funext u
      change (conwayRawProduct z (c • x)).2.1 u =
        c * (conwayRawProduct z x).2.1 u
      simp only [conwayRawProduct, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, conwayShortPairing, mul_add, add_mul,
        spinOperator_smul_pi]
      try simp_rw [Finset.mul_sum, Finset.sum_mul]
      try simp_rw [mul_ite, mul_zero]
      ring_nf
      try simp only [Finset.mul_sum, Finset.sum_mul]
      ring_nf
      simp only [mul_comm, mul_left_comm, mul_assoc]
      ring
    · funext t i
      change (conwayRawProduct z (c • x)).2.2 t i =
        c * (conwayRawProduct z x).2.2 t i
      simp only [conwayRawProduct, Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.trace_smul, mul_add, add_mul,
        spinOperator_smul_pi]
      try simp_rw [Finset.mul_sum, Finset.sum_mul]
      try simp_rw [mul_ite, mul_zero]
      ring_nf
      try simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]
      ring_nf
noncomputable def griessConwayDecodeLinear : ConwayRawSpace →ₗ[ℝ] GriessSpace where
  toFun := griessConwayDecode
  map_add' x y := by
    apply trialityBlocksEquiv.injective
    simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, map_add]
    apply Prod.ext
    · funext i
      rfl
    · apply Prod.ext
      · funext s p
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
        split_ifs <;> ring
      · apply Prod.ext
        · funext d e
          rfl
        · funext s k
          simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
          split_ifs <;> ring
  map_smul' c x := by
    apply trialityBlocksEquiv.injective
    simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, map_smul, RingHom.id_apply]
    apply Prod.ext
    · funext i
      rfl
    · apply Prod.ext
      · funext s p
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
        split_ifs <;> ring
      · apply Prod.ext
        · funext d e
          rfl
        · funext s k
          simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          split_ifs <;> ring

noncomputable def conwayRawProductLinear :
    ConwayRawSpace →ₗ[ℝ] ConwayRawSpace →ₗ[ℝ] ConwayRawSpace :=
  LinearMap.mk₂ ℝ conwayRawProduct conwayRawProduct_add_left
    conwayRawProduct_smul_left (fun x y z => conwayRawProduct_add_right y z x)
    (fun c x y => conwayRawProduct_smul_right c y x)

noncomputable def griessConwayProductLinear :
    GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] GriessSpace :=
  LinearMap.mk₂ ℝ (fun x y => griessConwayDecodeLinear
      (conwayRawProductLinear (griessConwayEncodeLinear x) (griessConwayEncodeLinear y)))
    (by intros; simp only [map_add, LinearMap.add_apply])
    (by intros; simp only [map_smul, LinearMap.smul_apply])
    (by intros; simp only [map_add])
    (by intros; simp only [map_smul])

set_option maxHeartbeats 1000000 in
-- The nested coordinate bilinear expressions exceed the default elaboration heartbeat budget.
/-- The structure-constant extension is exactly the concrete Conway product,
transported through the source dictionary. -/
theorem griessProd_eq_conwayRawProduct (x y : GriessSpace) :
    griessProd x y = griessConwayDecode
      (conwayRawProduct (griessConwayEncode x) (griessConwayEncode y)) := by
  have he : griessProd = griessConwayProductLinear := by
    apply LinearMap.pi_ext
    intro i a
    have ha : Pi.single i a = a • (Pi.single i (1 : ℝ) : GriessSpace) := by
      rw [← Pi.single_smul]
      simp only [smul_eq_mul, mul_one]
    rw [ha]
    simp only [map_smul]
    apply congrArg (fun w : GriessSpace →ₗ[ℝ] GriessSpace => a • w)
    apply LinearMap.pi_ext
    intro j b
    have hb : Pi.single j b = b • (Pi.single j (1 : ℝ) : GriessSpace) := by
      rw [← Pi.single_smul]
      simp only [smul_eq_mul, mul_one]
    rw [hb]
    simp only [map_smul]
    apply congrArg (fun w : GriessSpace => b • w)
    ext k
    simp [griessProd, griessProductFun, griessStructureConstant,
      griessConwayProductLinear, conwayRawProductLinear, griessConwayDecodeLinear,
      griessConwayEncodeLinear, Pi.single_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- Coordinate matrix of a Leech isometry in the standard real basis. -/
noncomputable def leechIsomMatrix (e : leechIsomSubgroup) : Matrix (Fin 24) (Fin 24) ℝ :=
  fun i j => e.val (Pi.single j 1) i

theorem leechIsom_inverse_coordinate (e : leechIsomSubgroup) (i k : Fin 24) :
    e.val.symm (Pi.single i 1) k = leechIsomMatrix e i k := by
  have h := e.property.1 (e.val.symm (Pi.single i 1)) (Pi.single k 1)
  rw [LinearEquiv.apply_symm_apply] at h
  simpa [stdPairingFun, leechIsomMatrix, Pi.single_apply] using h.symm

theorem leechIsomMatrix_transpose_mul (e : leechIsomSubgroup) :
    (leechIsomMatrix e).transpose * leechIsomMatrix e = 1 := by
  ext i j
  change (∑ k, e.val (Pi.single i 1) k * e.val (Pi.single j 1) k) = _
  have h := e.property.1 (Pi.single i 1) (Pi.single j 1)
  simpa [stdPairingFun, Pi.single_apply, Matrix.one_apply, eq_comm] using h

theorem conwayMatrixAction_eq_conjugate (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixAction e a = leechIsomMatrix e * a * (leechIsomMatrix e).transpose := by
  ext i j
  rw [← Matrix.toBilin'_single (conwayMatrixAction e a) i j,
    conwayMatrixAction_pairing, Matrix.toBilin'_apply]
  simp_rw [leechIsom_inverse_coordinate]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The Euclidean pairing on the matrix block. -/
noncomputable def conwayMatrixForm (a b : Matrix (Fin 24) (Fin 24) ℝ) : ℝ :=
  Matrix.trace (a.transpose * b)

theorem conwayMatrixForm_eq_sum (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm a b = ∑ i, ∑ j, a i j * b i j := by
  simp only [conwayMatrixForm, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem conwayMatrixAction_form (e : leechIsomSubgroup)
    (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixForm (conwayMatrixAction e a) (conwayMatrixAction e b) =
      conwayMatrixForm a b := by
  rw [conwayMatrixAction_eq_conjugate, conwayMatrixAction_eq_conjugate]
  simp only [conwayMatrixForm, Matrix.transpose_mul, Matrix.transpose_transpose]
  let m := leechIsomMatrix e
  have hm : m.transpose * m = 1 := leechIsomMatrix_transpose_mul e
  change Matrix.trace ((m * (a.transpose * m.transpose)) * (m * b * m.transpose)) = _
  calc
    _ = Matrix.trace (m * (a.transpose * b) * m.transpose) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc m.transpose m (b * m.transpose), hm, Matrix.one_mul]
    _ = Matrix.trace (m.transpose * m * (a.transpose * b)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hm, Matrix.one_mul]

/-- The local Leech action carries each preferred short vector to the preferred
representative of its permuted class, up to its unavoidable global sign. -/
theorem griessShortPermutation_vector (e : leechIsomSubgroup) (r : GriessShortIndex) :
    e.val (griessShortVector r) = griessShortVector (griessShortPermutation e r) ∨
      e.val (griessShortVector r) = -griessShortVector (griessShortPermutation e r) := by
  have hc : leechReduction (leechIntegralAction e (griessShortLatticeVector r)) =
      leechReduction (griessShortLatticeVector (griessShortPermutation e r)) :=
    (griessShortPermutation_class e r).symm
  have hn : leechSquareSum (leechIntegralAction e (griessShortLatticeVector r)).val = 32 := by
    rw [leechIntegralAction_squareSum]
    exact griessShortIntegral_squareSum r
  have hv := leechShort_same_class
    (leechIntegralAction e (griessShortLatticeVector r))
    (griessShortLatticeVector (griessShortPermutation e r)) hn
    (griessShortIntegral_squareSum _) hc
  change e.val (leechCoordinateEmbedding (griessShortLatticeVector r).val) = _ ∨
    e.val (leechCoordinateEmbedding (griessShortLatticeVector r).val) = _
  rw [← leechIntegralAction_embedding]
  rcases hv with hv | hv
  · left
    rw [hv]
    rfl
  · right
    rw [hv]
    rw [Submodule.coe_neg, map_neg]
    rfl

/-- Outer products are independent of the representative sign. -/
theorem griessShortPermutation_outer (e : leechIsomSubgroup) (r : GriessShortIndex)
    (i j : Fin 24) :
    e.val (griessShortVector r) i * e.val (griessShortVector r) j =
      griessShortVector (griessShortPermutation e r) i *
        griessShortVector (griessShortPermutation e r) j := by
  rcases griessShortPermutation_vector e r with h | h
  · rw [h]
  · rw [h]
    simp only [Pi.neg_apply, neg_mul_neg]

/-- The raw local action is the product of its three independently defined blocks. -/
theorem localConwayRawRepresentation_apply (f : localFiberSubgroup) (x : ConwayRawSpace) :
    localConwayRawRepresentation f x =
      (conwayMatrixAction f.val.2 x.1,
        (localShortRepresentation f x.2.1, localTensorRepresentation f x.2.2)) := by
  simp only [localConwayRawRepresentation, MonoidHom.comp_apply, MonoidHom.prod_apply,
    coordinateProdGLHom_apply]
  rfl

/-- Coordinate transport intertwines the local dictionary action and raw action. -/
theorem localGriessRepresentation_encode (f : localFiberSubgroup) (x : GriessSpace) :
    griessConwayEncode (localGriessRepresentation f x) =
      localConwayRawRepresentation f (griessConwayEncode x) := by
  change (griessConwayEquiv (griessConwayEquiv.symm
    (localConwayRepresentation f (griessConwayEquiv x)))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The Euclidean pairing of Conway's three orthogonal coordinate blocks. -/
noncomputable def conwayRawForm (x y : ConwayRawSpace) : ℝ :=
  conwayMatrixForm x.1 y.1 + (∑ r, x.2.1 r * y.2.1 r) +
    conwayTensorForm x.2.2 y.2.2

/-- The source dictionary preserves the full pairing in the raw coordinates. -/
theorem griessForm_eq_conwayRawForm (x y : GriessSpace) :
    griessForm x y = conwayRawForm (griessConwayEncode x) (griessConwayEncode y) := by
  rw [griessForm_eq_conwayCoordinates, conwayRawForm, conwayMatrixForm_eq_sum]
  rfl

/-- The local fiber-product action preserves all three summands of the raw form. -/
theorem localConwayRawRepresentation_form (f : localFiberSubgroup) (x y : ConwayRawSpace) :
    conwayRawForm (localConwayRawRepresentation f x) (localConwayRawRepresentation f y) =
      conwayRawForm x y := by
  rw [localConwayRawRepresentation_apply, localConwayRawRepresentation_apply]
  simp only [conwayRawForm]
  rw [conwayMatrixAction_form, localShortRepresentation_pairing,
    localTensorRepresentation_pairing]

/-- The local Griess representation preserves the prescribed source form. -/
theorem localGriessRepresentation_form (f : localFiberSubgroup) (x y : GriessSpace) :
    griessForm (localGriessRepresentation f x) (localGriessRepresentation f y) =
      griessForm x y := by
  rw [griessForm_eq_conwayRawForm, griessForm_eq_conwayRawForm,
    localGriessRepresentation_encode, localGriessRepresentation_encode,
    localConwayRawRepresentation_form]

/-- Orthogonality descends from the local fiber product to the actual quotient H. -/
theorem rhoLocal_form (h : H) (x y : GriessSpace) :
    griessForm (rhoLocal h x) (rhoLocal h y) = griessForm x y := by
  refine Quotient.inductionOn h ?_
  intro f
  exact localGriessRepresentation_form f x y

theorem conwayShortPairing_eq_bilin (a : Matrix (Fin 24) (Fin 24) ℝ)
    (r : GriessShortIndex) :
    conwayShortPairing a r = Matrix.toBilin' a (griessShortVector r) (griessShortVector r) := by
  rw [Matrix.toBilin'_apply]
  unfold conwayShortPairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conwayShortPairing_covariant (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (r : GriessShortIndex) :
    conwayShortPairing (conwayMatrixAction e a) (griessShortPermutation e r) =
      conwayShortPairing a r := by
  rw [conwayShortPairing_eq_bilin, conwayShortPairing_eq_bilin]
  have h := conwayMatrixAction_pairing e a (e.val (griessShortVector r))
    (e.val (griessShortVector r))
  simp only [LinearEquiv.symm_apply_apply] at h
  rcases griessShortPermutation_vector e r with he | he
  · rwa [he] at h
  · rw [he] at h
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using h

theorem localShortRepresentation_matrix_product (f : localFiberSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (x : GriessShortIndex → ℝ) :
    localShortRepresentation f (fun r => conwayShortPairing a r * x r) =
      fun r => conwayShortPairing (conwayMatrixAction f.val.2 a) r *
        localShortRepresentation f x r := by
  funext r
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective r
  change localShortOperator f (fun r => conwayShortPairing a r * x r)
      (griessShortPermutation f.val.2 s) = _
  rw [localShortOperator_image, conwayShortPairing_covariant]
  change _ = conwayShortPairing a s * localShortOperator f x (griessShortPermutation f.val.2 s)
  rw [localShortOperator_image]
  ring

theorem conwayMatrixAction_mul (e : leechIsomSubgroup)
    (a b : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixAction e (a * b) = conwayMatrixAction e a * conwayMatrixAction e b := by
  simp only [conwayMatrixAction_eq_conjugate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (leechIsomMatrix e).transpose (leechIsomMatrix e)]
  rw [leechIsomMatrix_transpose_mul, Matrix.one_mul]

theorem conwayMatrixAction_trace (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) :
    Matrix.trace (conwayMatrixAction e a) = Matrix.trace a := by
  rw [conwayMatrixAction_eq_conjugate, Matrix.trace_mul_cycle,
    leechIsomMatrix_transpose_mul, Matrix.one_mul]

theorem leechIsomMatrix_mulVec (e : leechIsomSubgroup) (x : Fin 24 → ℝ) :
    leechIsomMatrix e *ᵥ x = e.val x := by
  change LinearMap.toMatrix' e.val.toLinearMap *ᵥ x = _
  exact LinearMap.toMatrix'_mulVec _ _

theorem conwayMatrixAction_short_outer (e : leechIsomSubgroup) (r : GriessShortIndex) :
    conwayMatrixAction e (Matrix.vecMulVec (griessShortVector r) (griessShortVector r)) =
      Matrix.vecMulVec (griessShortVector (griessShortPermutation e r))
        (griessShortVector (griessShortPermutation e r)) := by
  rw [conwayMatrixAction_eq_conjugate, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose, leechIsomMatrix_mulVec]
  ext i j
  exact griessShortPermutation_outer e r i j

theorem conwayMatrixAction_one (e : leechIsomSubgroup) :
    conwayMatrixAction e (1 : Matrix (Fin 24) (Fin 24) ℝ) = 1 := by
  rw [conwayMatrixAction_eq_conjugate, Matrix.mul_one]
  exact mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul e)

theorem conwayTensorCoefficient_eq_matrix (r : GriessShortIndex) :
    (conwayTensorCoefficient r : Matrix (Fin 24) (Fin 24) ℝ) =
      (1 : Matrix (Fin 24) (Fin 24) ℝ) -
        (2 : ℝ) • Matrix.vecMulVec (griessShortVector r) (griessShortVector r) := by
  ext i j
  simp only [conwayTensorCoefficient, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

theorem conwayTensorCoefficient_covariant (e : leechIsomSubgroup) (r : GriessShortIndex) :
    conwayMatrixAction e (conwayTensorCoefficient r) =
      conwayTensorCoefficient (griessShortPermutation e r) := by
  rw [conwayTensorCoefficient_eq_matrix, conwayTensorCoefficient_eq_matrix,
    map_sub, map_smul, conwayMatrixAction_one, conwayMatrixAction_short_outer]

theorem conwayMatrixAction_mulVec (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (x : Fin 24 → ℝ) :
    conwayMatrixAction e a *ᵥ e.val x = e.val (a *ᵥ x) := by
  rw [conwayMatrixAction_eq_conjugate, ← leechIsomMatrix_mulVec e x]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec x (leechIsomMatrix e).transpose (leechIsomMatrix e),
    leechIsomMatrix_transpose_mul, Matrix.one_mulVec, leechIsomMatrix_mulVec]

theorem localSpin_short_intertwine (f : localFiberSubgroup) (r : GriessShortIndex)
    (x : SpinSpace) :
    f.val.1.val (spinRepresentation (griessShortQ r) x) =
      qSign (localShortPhase f r) • spinRepresentation (griessShortQ
        (griessShortPermutation f.val.2 r)) (f.val.1.val x) := by
  have h := LinearEquiv.congr_fun (spinConjugation_representation f.val.1 (griessShortQ r))
    (f.val.1.val x)
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply] at h
  rw [griessShortQ_image, map_mul, LinearEquiv.mul_apply,
    spinRepresentation_central] at h
  exact h.symm

noncomputable def conwayTensorShortOperator (r : GriessShortIndex) :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  conwayTensorCoordinates.toLinearMap.comp
    ((TensorProduct.map (spinRepresentation (griessShortQ r)).toLinearMap
      (Matrix.toLin' (conwayTensorCoefficient r))).comp
      conwayTensorCoordinates.symm.toLinearMap)

theorem conwayTensorShortOperator_tmul (r : GriessShortIndex) (a : SpinSpace)
    (b : Fin 24 → ℝ) :
    conwayTensorShortOperator r (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)) =
      conwayTensorCoordinates (spinRepresentation (griessShortQ r) a ⊗ₜ[ℝ]
        (conwayTensorCoefficient r *ᵥ b)) := by
  simp only [conwayTensorShortOperator, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    Matrix.toLin'_apply]

theorem localTensorRepresentation_coordinates (f : localFiberSubgroup)
    (x : SpinSpace ⊗[ℝ] (Fin 24 → ℝ)) :
    localTensorRepresentation f (conwayTensorCoordinates x) =
      conwayTensorCoordinates (localTensorAction f x) := by
  simp only [localTensorRepresentation, MonoidHom.comp_apply,
    coordinateGLTransport_apply, LinearEquiv.symm_apply_apply]

theorem conwayTensorShortOperator_intertwine (f : localFiberSubgroup)
    (r : GriessShortIndex) (x : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation f (conwayTensorShortOperator r x) =
      qSign (localShortPhase f r) •
        conwayTensorShortOperator (griessShortPermutation f.val.2 r)
          (localTensorRepresentation f x) := by
  obtain ⟨x, rfl⟩ := conwayTensorCoordinates.surjective x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [conwayTensorShortOperator_tmul, localTensorRepresentation_coordinates]
    change conwayTensorCoordinates
      (f.val.1.val (spinRepresentation (griessShortQ r) a) ⊗ₜ[ℝ]
        f.val.2.val (conwayTensorCoefficient r *ᵥ b)) = _
    rw [localSpin_short_intertwine]
    rw [← conwayMatrixAction_mulVec, conwayTensorCoefficient_covariant]
    rw [localTensorRepresentation_coordinates]
    change _ = qSign (localShortPhase f r) •
      conwayTensorShortOperator (griessShortPermutation f.val.2 r)
        (conwayTensorCoordinates (f.val.1.val a ⊗ₜ[ℝ] f.val.2.val b))
    rw [conwayTensorShortOperator_tmul, ← TensorProduct.smul_tmul', map_smul]
  | add a b ha hb =>
    simp only [map_add, smul_add, ha, hb]

theorem conwayTensorCoefficient_symmetric (r : GriessShortIndex) (i j : Fin 24) :
    conwayTensorCoefficient r i j = conwayTensorCoefficient r j i := by
  simp only [conwayTensorCoefficient, eq_comm]
  ring

theorem spinOperator_mul_fun (q : Q) (a : SpinSpace) (b : ℝ) (t : SpinIndex) :
    spinOperator q (fun v => a v * b) t = b * spinRepresentation q a t := by
  have h : (fun v => a v * b) = b • a := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [h, map_smul]
  rfl

theorem conwayTensorShortOperator_apply (r : GriessShortIndex)
    (x : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    conwayTensorShortOperator r x t i =
      ∑ j, spinOperator (griessShortQ r) (fun v => x v j) t *
        conwayTensorCoefficient r j i := by
  obtain ⟨x, rfl⟩ := conwayTensorCoordinates.surjective x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [conwayTensorShortOperator_tmul]
    simp only [conwayTensorCoordinates_tmul]
    simp_rw [spinOperator_mul_fun, conwayTensorCoefficient_symmetric r _ i]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, spinOperator, LinearMap.coe_mk, AddHom.coe_mk,
      mul_add, add_mul, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb]

/-- The spin-tensor / spin-tensor contribution to the short block. -/
noncomputable def conwayTensorTensorShort (x y : SpinIndex → Fin 24 → ℝ)
    (r : GriessShortIndex) : ℝ :=
  conwayTensorForm (conwayTensorShortOperator r x) y / 8

theorem conwayTensorTensorShort_apply (x y : SpinIndex → Fin 24 → ℝ)
    (r : GriessShortIndex) :
    conwayTensorTensorShort x y r =
      (∑ t, ∑ i, ∑ j,
        spinOperator (griessShortQ r) (fun v => x v i) t * y t j *
          conwayTensorCoefficient r i j) / 8 := by
  simp only [conwayTensorTensorShort, conwayTensorForm, LinearMap.mk₂_apply,
    conwayTensorShortOperator_apply, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conwayTensorTensorShort_covariant (f : localFiberSubgroup)
    (x y : SpinIndex → Fin 24 → ℝ) :
    localShortRepresentation f (conwayTensorTensorShort x y) =
      conwayTensorTensorShort (localTensorRepresentation f x) (localTensorRepresentation f y) := by
  funext r
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective r
  change localShortOperator f (conwayTensorTensorShort x y) (griessShortPermutation f.val.2 s) = _
  rw [localShortOperator_image]
  unfold conwayTensorTensorShort
  have h := localTensorRepresentation_pairing f (conwayTensorShortOperator s x) y
  rw [conwayTensorShortOperator_intertwine] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hc := qSign_sq (localShortPhase f s)
  have hsign : qSign (localShortPhase f s) *
      conwayTensorForm (conwayTensorShortOperator s x) y =
    conwayTensorForm (conwayTensorShortOperator (griessShortPermutation f.val.2 s)
      (localTensorRepresentation f x)) (localTensorRepresentation f y) := by
    rw [← h, ← mul_assoc, hc, one_mul]
  rw [← hsign]
  ring

/-- The short / spin-tensor contribution to the tensor block. -/
noncomputable def conwayShortTensorProduct (x : GriessShortIndex → ℝ)
    (y : SpinIndex → Fin 24 → ℝ) : SpinIndex → Fin 24 → ℝ :=
  (1 / 8 : ℝ) • ∑ r, x r • conwayTensorShortOperator r y

theorem conwayShortTensorProduct_apply (x : GriessShortIndex → ℝ)
    (y : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    conwayShortTensorProduct x y t i =
      (∑ r, ∑ j, x r * spinOperator (griessShortQ r) (fun v => y v j) t *
        conwayTensorCoefficient r j i) / 8 := by
  simp only [conwayShortTensorProduct, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    conwayTensorShortOperator_apply, Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conwayShortTensorProduct_covariant (f : localFiberSubgroup)
    (x : GriessShortIndex → ℝ) (y : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation f (conwayShortTensorProduct x y) =
      conwayShortTensorProduct (localShortRepresentation f x) (localTensorRepresentation f y) := by
  unfold conwayShortTensorProduct
  rw [map_smul, map_sum]
  apply congrArg (fun z : SpinIndex → Fin 24 → ℝ => (1 / 8 : ℝ) • z)
  rw [← Equiv.sum_comp (griessShortPermutation f.val.2)
    (fun r => localShortRepresentation f x r •
      conwayTensorShortOperator r (localTensorRepresentation f y))]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul, conwayTensorShortOperator_intertwine]
  change x r • (qSign (localShortPhase f r) • _) =
    localShortOperator f x (griessShortPermutation f.val.2 r) • _
  rw [localShortOperator_image, smul_smul]
  rw [mul_comm (x r)]

noncomputable def conwayTensorIncl :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun x := (0, (0, x))
  map_add' x y := by
    apply Prod.ext
    · exact (zero_add _).symm
    · apply Prod.ext
      · exact (zero_add _).symm
      · rfl
  map_smul' c x := by
    simp only [Prod.smul_mk, smul_zero, RingHom.id_apply]

noncomputable def conwayTensorTensorMatrix :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ]
      Matrix (Fin 24) (Fin 24) ℝ :=
  LinearMap.mk₂ ℝ (fun x y =>
      (conwayRawProductLinear (conwayTensorIncl x) (conwayTensorIncl y)).1)
    (by intros; simp only [map_add, LinearMap.add_apply, Prod.fst_add])
    (by intros; simp only [map_smul, LinearMap.smul_apply, Prod.smul_fst])
    (by intros; simp only [map_add, Prod.fst_add])
    (by intros; simp only [map_smul, Prod.smul_fst])

theorem conwayTensorTensorMatrix_apply (x y : SpinIndex → Fin 24 → ℝ)
    (i j : Fin 24) :
    conwayTensorTensorMatrix x y i j =
      (∑ t, ((∑ k, x t k * y t k) * (if i = j then 1 else 0) +
        4 * x t i * y t j + 4 * y t i * x t j)) / 8 := by
  simp [conwayTensorTensorMatrix, conwayTensorIncl, conwayRawProductLinear,
    conwayRawProduct, Matrix.zero_apply]

theorem conwayMatrixAction_vecMulVec (e : leechIsomSubgroup)
    (x y : Fin 24 → ℝ) :
    conwayMatrixAction e (Matrix.vecMulVec x y) = Matrix.vecMulVec (e.val x) (e.val y) := by
  rw [conwayMatrixAction_eq_conjugate, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]
  simp only [leechIsomMatrix_mulVec]

theorem conwayTensorTensorMatrix_tmul (a a' : SpinSpace) (b b' : Fin 24 → ℝ) :
    conwayTensorTensorMatrix (conwayTensorCoordinates (a ⊗ₜ[ℝ] b))
      (conwayTensorCoordinates (a' ⊗ₜ[ℝ] b')) =
      (spinPairing a a' / 8) •
        ((stdPairingFun b b') • (1 : Matrix (Fin 24) (Fin 24) ℝ) +
          (4 : ℝ) • Matrix.vecMulVec b b' + (4 : ℝ) • Matrix.vecMulVec b' b) := by
  ext i j
  rw [conwayTensorTensorMatrix_apply]
  simp only [conwayTensorCoordinates_tmul, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul, spinPairing, stdPairingFun]
  have h (t : SpinIndex) : (∑ k, (a t * b k) * (a' t * b' k)) =
      a t * a' t * ∑ k, b k * b' k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [h]
  rw [div_mul_eq_mul_div]
  apply congrArg (fun z : ℝ => z / 8)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem conwayTensorTensorMatrix_covariant (f : localFiberSubgroup)
    (x y : SpinIndex → Fin 24 → ℝ) :
    conwayMatrixAction f.val.2 (conwayTensorTensorMatrix x y) =
      conwayTensorTensorMatrix (localTensorRepresentation f x) (localTensorRepresentation f y) := by
  obtain ⟨x, rfl⟩ := conwayTensorCoordinates.surjective x
  obtain ⟨y, rfl⟩ := conwayTensorCoordinates.surjective y
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul a' b' =>
      rw [localTensorRepresentation_coordinates, localTensorRepresentation_coordinates]
      change _ = conwayTensorTensorMatrix
        (conwayTensorCoordinates (f.val.1.val a ⊗ₜ[ℝ] f.val.2.val b))
        (conwayTensorCoordinates (f.val.1.val a' ⊗ₜ[ℝ] f.val.2.val b'))
      rw [conwayTensorTensorMatrix_tmul, conwayTensorTensorMatrix_tmul]
      simp only [map_smul, map_add, conwayMatrixAction_one, conwayMatrixAction_vecMulVec]
      rw [f.val.1.property.2, f.val.2.property.1]
    | add u v hu hv =>
      simp only [map_add, hu, hv]
  | add u v hu hv =>
    simp only [map_add, LinearMap.add_apply, hu, hv]

noncomputable def conwayMatrixIncl :
    Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] ConwayRawSpace where
  toFun a := (a, (0, 0))
  map_add' a b := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> exact (zero_add _).symm
  map_smul' c a := by
    simp only [Prod.smul_mk, smul_zero, RingHom.id_apply]

noncomputable def conwayMatrixTensorProduct :
    Matrix (Fin 24) (Fin 24) ℝ →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ]
      (SpinIndex → Fin 24 → ℝ) :=
  LinearMap.mk₂ ℝ (fun a y =>
      (conwayRawProductLinear (conwayMatrixIncl a) (conwayTensorIncl y)).2.2)
    (by intros; simp only [map_add, LinearMap.add_apply, Prod.snd_add])
    (by intros; simp only [map_smul, LinearMap.smul_apply, Prod.smul_snd])
    (by intros; simp only [map_add, Prod.snd_add])
    (by intros; simp only [map_smul, Prod.smul_snd])

theorem conwayMatrixTensorProduct_apply (a : Matrix (Fin 24) (Fin 24) ℝ)
    (y : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    conwayMatrixTensorProduct a y t i =
      (∑ j, a j i * y t j) + Matrix.trace a / 8 * y t i := by
  simp [conwayMatrixTensorProduct, conwayMatrixIncl, conwayTensorIncl,
    conwayRawProductLinear, conwayRawProduct, Matrix.zero_apply, spinOperator]

theorem conwayMatrixTensorProduct_tmul (a : Matrix (Fin 24) (Fin 24) ℝ)
    (u : SpinSpace) (v : Fin 24 → ℝ) :
    conwayMatrixTensorProduct a (conwayTensorCoordinates (u ⊗ₜ[ℝ] v)) =
      conwayTensorCoordinates (u ⊗ₜ[ℝ]
        (a.transpose *ᵥ v + (Matrix.trace a / 8) • v)) := by
  funext t i
  rw [conwayMatrixTensorProduct_apply]
  simp only [conwayTensorCoordinates_tmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

theorem conwayMatrixAction_transpose (e : leechIsomSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixAction e a.transpose = (conwayMatrixAction e a).transpose := by
  simp only [conwayMatrixAction_eq_conjugate, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem conwayMatrixTensorProduct_covariant (f : localFiberSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (y : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation f (conwayMatrixTensorProduct a y) =
      conwayMatrixTensorProduct (conwayMatrixAction f.val.2 a) (localTensorRepresentation f y) := by
  obtain ⟨y, rfl⟩ := conwayTensorCoordinates.surjective y
  induction y using TensorProduct.inductionOn with
  | tmul u v =>
    rw [conwayMatrixTensorProduct_tmul, localTensorRepresentation_coordinates,
      localTensorRepresentation_coordinates]
    change conwayTensorCoordinates (f.val.1.val u ⊗ₜ[ℝ]
        f.val.2.val (a.transpose *ᵥ v + (Matrix.trace a / 8) • v)) =
      conwayMatrixTensorProduct (conwayMatrixAction f.val.2 a)
        (conwayTensorCoordinates (f.val.1.val u ⊗ₜ[ℝ] f.val.2.val v))
    rw [conwayMatrixTensorProduct_tmul, map_add, map_smul,
      ← conwayMatrixAction_mulVec, conwayMatrixAction_transpose, conwayMatrixAction_trace]
  | add u v hu hv =>
    simp only [map_add, hu, hv]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
