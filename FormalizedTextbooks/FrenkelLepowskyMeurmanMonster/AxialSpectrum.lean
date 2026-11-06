/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Multiplication by Conway's signed short axes and exclusion of their midpoint eigenvalue 32.
Source: Conway, Invent. Math. 79 (1985), Appendix 6, printed page 539.
The tensor block has annihilator roots 0, 2, 16. The matrix and short-coordinate
arguments prove midpoint exclusion using the genuine lattice geometry and central phases.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixAxisKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import Mathlib.Tactic.NoncommRing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

abbrev ConwayTensorSpace := SpinIndex → Fin 24 → ℝ

/-- Spin involution associated to the axis's preferred norm-four short lift. -/
noncomputable def conwayAxisSpin (p : Fin 276) : Module.End ℝ ConwayTensorSpace where
  toFun T t i := spinOperator (griessShortQ (Sum.inl (0, p))) (fun u => T u i) t
  map_add' T U := by
    funext t i
    exact congrFun ((spinOperator _).map_add (fun u => T u i) (fun u => U u i)) t
  map_smul' c T := by
    funext t i
    exact congrFun ((spinOperator _).map_smul c (fun u => T u i)) t

/-- Orthogonal spatial projection onto the coordinate difference underlying the axis. -/
noncomputable def conwayAxisTensorProjection (p : Fin 276) : Module.End ℝ ConwayTensorSpace where
  toFun T t i := (∑ j, T t j * conwayAxisDifference p j) * conwayAxisDifference p i / 2
  map_add' T U := by
    funext t i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]
  map_smul' c T := by
    funext t i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc c]
    rw [← Finset.mul_sum]
    ring

/-- The spin factor is a genuine involution, using the proven square of the short lift. -/
theorem conwayAxisSpin_square (p : Fin 276) : conwayAxisSpin p * conwayAxisSpin p = 1 := by
  apply LinearMap.ext
  intro T
  funext t i
  have h := congrArg (fun F : SpinSpace →ₗ[ℝ] SpinSpace => F (fun u => T u i) t)
    (spinOperator_mul (griessShortQ (Sum.inl (0, p))) (griessShortQ (Sum.inl (0, p))))
  rw [griessShortQ_square, spinOperator_one] at h
  exact h.symm

/-- The spatial factor is a genuine rank-one projection. -/
theorem conwayAxisTensorProjection_square (p : Fin 276) :
    conwayAxisTensorProjection p * conwayAxisTensorProjection p = conwayAxisTensorProjection p := by
  apply LinearMap.ext
  intro T
  funext t i
  change (∑ j, ((∑ k, T t k * conwayAxisDifference p k) * conwayAxisDifference p j / 2) *
      conwayAxisDifference p j) * conwayAxisDifference p i / 2 = _
  have he (j : Fin 24) :
      ((∑ k, T t k * conwayAxisDifference p k) * conwayAxisDifference p j / 2) *
        conwayAxisDifference p j =
      ((∑ k, T t k * conwayAxisDifference p k) / 2) *
        (conwayAxisDifference p j * conwayAxisDifference p j) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, conwayAxisDifference_square_sum]
  change _ = (∑ k, T t k * conwayAxisDifference p k) * conwayAxisDifference p i / 2
  ring

/-- Spin and spatial projection operate on different tensor factors and commute. -/
theorem conwayAxisSpin_projection_commute (p : Fin 276) :
    conwayAxisSpin p * conwayAxisTensorProjection p =
      conwayAxisTensorProjection p * conwayAxisSpin p := by
  apply LinearMap.ext
  intro T
  funext t i
  simp only [Module.End.mul_apply, conwayAxisSpin, conwayAxisTensorProjection,
    LinearMap.coe_mk, AddHom.coe_mk, spinOperator]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- The tensor block's axial multiplication operator, with the Conway normalization. -/
noncomputable def conwayAxisTensorOperator (p : Fin 276) : Module.End ℝ ConwayTensorSpace :=
  1 - conwayAxisSpin p + 8 * conwayAxisTensorProjection p +
    8 * (conwayAxisSpin p * conwayAxisTensorProjection p)

private theorem involution_projection_polynomial {A : Type*} [Ring A]
    (S P : A) (hS : S * S = 1) (hP : P * P = P) (hSP : S * P = P * S) :
    let L := 1 - S + 8 * P + 8 * (S * P)
    L * (L - 2) * (L - 16) = 0 := by
  dsimp only
  have hSS (x : A) : S * (S * x) = x := by rw [← mul_assoc, hS, one_mul]
  have hPP (x : A) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  have hSP' (x : A) : S * (P * x) = P * (S * x) := by rw [← mul_assoc, hSP, mul_assoc]
  noncomm_ring [hSS, hPP, hSP', hS, hP, hSP]

/-- The tensor block satisfies the polynomial with roots zero, two, and sixteen. -/
theorem conwayAxisTensorOperator_polynomial (p : Fin 276) :
    conwayAxisTensorOperator p * (conwayAxisTensorOperator p - 2) *
      (conwayAxisTensorOperator p - 16) = 0 := by
  exact
    involution_projection_polynomial (conwayAxisSpin p) (conwayAxisTensorProjection p)
      (conwayAxisSpin_square p) (conwayAxisTensorProjection_square p)
      (conwayAxisSpin_projection_commute p)
/-- The spatial and spin parts of axial multiplication in explicit tensor coordinates. -/
theorem conwayAxisTensorOperator_apply (p : Fin 276) (T : ConwayTensorSpace)
    (t : SpinIndex) (i : Fin 24) :
    conwayAxisTensorOperator p T t i = T t i - conwayAxisSpin p T t i +
      4 * (∑ j, T t j * conwayAxisDifference p j) * conwayAxisDifference p i +
      4 * (∑ j, conwayAxisSpin p T t j * conwayAxisDifference p j) * conwayAxisDifference p i := by
  have hc := congrArg (fun L : Module.End ℝ ConwayTensorSpace => L T t i)
    (conwayAxisSpin_projection_commute p)
  simp only [Module.End.mul_apply] at hc
  simp only [conwayAxisTensorOperator, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, Module.End.mul_apply, Module.End.ofNat_apply,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.ofNat_apply]
  rw [hc]
  change T t i - conwayAxisSpin p T t i +
      8 * ((∑ j, T t j * conwayAxisDifference p j) * conwayAxisDifference p i / 2) +
      8 * ((∑ j, conwayAxisSpin p T t j * conwayAxisDifference p j) *
        conwayAxisDifference p i / 2) = _
  ring

/-- The tensor block has no eigenvalues besides the three source values. -/
theorem conwayAxisTensorOperator_eigenvalue (p : Fin 276) (c : ℝ) (T : ConwayTensorSpace)
    (hT : T ≠ 0) (hc : conwayAxisTensorOperator p T = c • T) : c = 0 ∨ c = 2 ∨ c = 16 := by
  have hp := congrArg (fun L : Module.End ℝ ConwayTensorSpace => L T)
    (conwayAxisTensorOperator_polynomial p)
  have h2 : (conwayAxisTensorOperator p - 2) T = (c - 2) • T := by
    simp only [LinearMap.sub_apply, hc, Module.End.ofNat_apply]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    change c • T - (2 : ℝ) • T = (c - 2) • T
    rw [sub_smul]
  have h16 : (conwayAxisTensorOperator p - 16) T = (c - 16) • T := by
    simp only [LinearMap.sub_apply, hc, Module.End.ofNat_apply]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    change c • T - (16 : ℝ) • T = (c - 16) • T
    rw [sub_smul]
  rw [Module.End.mul_apply, Module.End.mul_apply, h16, map_smul, h2] at hp
  simp only [map_smul, hc, smul_smul] at hp
  simp only [LinearMap.zero_apply] at hp
  rw [mul_assoc] at hp
  change ((c - 16) * ((c - 2) * c)) • T = 0 at hp
  have hz : (c - 16) * ((c - 2) * c) = 0 := (smul_eq_zero.mp hp).resolve_right hT
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inl h

private theorem conwayAxisMatrix_trace (p : Fin 276) : Matrix.trace (conwayAxisMatrix p) = 8 := by
  change (∑ i, conwayAxisMatrix p i i) = 8
  simp_rw [conwayAxisMatrix_rank_one, mul_assoc]
  rw [← Finset.mul_sum, conwayAxisDifference_square_sum]
  norm_num

/-- Multiplying an actual pure spin tensor by the axis remains in the tensor block,
and its operator is exactly the source-normalized `conwayAxisTensorOperator`. -/
theorem conwayAxis_raw_tensor (p : Fin 276) (T : ConwayTensorSpace) :
    conwayRawProduct (griessConwayEncode (conwayAxis p)) (0, (0, T)) =
      (0, (0, conwayAxisTensorOperator p T)) := by
  rw [conwayAxis_encode]
  let r0 : GriessShortIndex := Sum.inl (0, p)
  let X : GriessShortIndex → ℝ := (-8 : ℝ) • Pi.single r0 1
  have hx0 : X r0 = -8 := by simp [X]
  have hx (r : GriessShortIndex) (hr : r ≠ r0) : X r = 0 := by simp [X, hr]
  have hmat (t : SpinIndex) (i : Fin 24) :
      (∑ j, conwayAxisMatrix p j i * T t j) =
        4 * (∑ j, T t j * conwayAxisDifference p j) * conwayAxisDifference p i := by
    simp_rw [conwayAxisMatrix_rank_one]
    have he (j : Fin 24) :
        (4 * conwayAxisDifference p j * conwayAxisDifference p i) * T t j =
        (4 * conwayAxisDifference p i) * (T t j * conwayAxisDifference p j) := by ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    ring
  have hxt (t : SpinIndex) (i : Fin 24) :
      (∑ r, ∑ j, X r * spinOperator (griessShortQ r) (fun v => T v j) t *
        conwayTensorCoefficient r j i) =
      -8 * (conwayAxisSpin p T t i -
        4 * (∑ j, conwayAxisSpin p T t j * conwayAxisDifference p j) *
          conwayAxisDifference p i) := by
    rw [Finset.sum_eq_single r0]
    · rw [hx0]
      change (∑ j, -8 * conwayAxisSpin p T t j *
          ((if j = i then 1 else 0) - 2 * griessShortVector (Sum.inl (0, p)) j *
            griessShortVector (Sum.inl (0, p)) i)) = _
      have he (j : Fin 24) :
          -8 * conwayAxisSpin p T t j *
            ((if j = i then 1 else 0) - 2 * griessShortVector (Sum.inl (0, p)) j *
              griessShortVector (Sum.inl (0, p)) i) =
          -8 * (conwayAxisSpin p T t j * (if j = i then 1 else 0) -
            (4 * conwayAxisDifference p i) *
              (conwayAxisSpin p T t j * conwayAxisDifference p j)) := by
        have ho : 2 * griessShortVector (Sum.inl (0, p)) j *
            griessShortVector (Sum.inl (0, p)) i =
            4 * conwayAxisDifference p j * conwayAxisDifference p i := by
          nlinarith [conwayAxis_short_outer p j i]
        rw [ho]
        ring
      simp_rw [he]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    · intro r _ hr
      simp [hx r hr]
    · simp
  change conwayRawProduct (conwayAxisMatrix p, (X, 0)) (0, (0, T)) = _
  apply Prod.ext
  · funext i j
    simp [conwayRawProduct]
  · apply Prod.ext
    · funext u
      simp [conwayRawProduct, conwayShortPairing, spinOperator]
    · funext t i
      dsimp only [conwayRawProduct]
      simp only [Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero, add_zero]
      rw [hmat, conwayAxisMatrix_trace, hxt, conwayAxisTensorOperator_apply]
      ring

/-- Include the pure tensor block into the three raw Conway blocks. -/
def conwayTensorRawEmbedding : ConwayTensorSpace →ₗ[ℝ] ConwayRawSpace :=
  (LinearMap.inr ℝ (Matrix (Fin 24) (Fin 24) ℝ)
    ((GriessShortIndex → ℝ) × ConwayTensorSpace)).comp
      (LinearMap.inr ℝ (GriessShortIndex → ℝ) ConwayTensorSpace)

/-- The actual embedding of the pure tensor block into the Griess algebra. -/
noncomputable def conwayTensorEmbedding : ConwayTensorSpace →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp conwayTensorRawEmbedding

/-- The dictionary encoding recovers the pure tensor coordinates. -/
theorem conwayTensorEmbedding_encode (T : ConwayTensorSpace) :
    griessConwayEncode (conwayTensorEmbedding T) = (0, (0, T)) :=
  griessConwayEncode_decode _ (fun _ _ => rfl)

/-- The tensor block embeds faithfully in the concrete Griess space. -/
theorem conwayTensorEmbedding_injective : Function.Injective conwayTensorEmbedding := by
  intro T U h
  have he := congrArg griessConwayEncode h
  rw [conwayTensorEmbedding_encode, conwayTensorEmbedding_encode] at he
  exact congrArg (fun x : ConwayRawSpace => x.2.2) he

/-- The tensor-block spectrum concerns the actual multiplication in the specified Griess algebra. -/
theorem conwayAxis_tensor_product (p : Fin 276) (T : ConwayTensorSpace) :
    griessProd (conwayAxis p) (conwayTensorEmbedding T) =
      conwayTensorEmbedding (conwayAxisTensorOperator p T) := by
  rw [griessProd_eq_conwayRawProduct, conwayTensorEmbedding_encode, conwayAxis_raw_tensor]
  rfl

/-- An actual pure tensor eigenvector of axial multiplication has eigenvalue zero, two,
or sixteen. -/
theorem conwayAxis_tensor_eigenvalue (p : Fin 276) (c : ℝ) (T : ConwayTensorSpace)
    (hT : T ≠ 0)
    (hc : griessProd (conwayAxis p) (conwayTensorEmbedding T) = c • conwayTensorEmbedding T) :
    c = 0 ∨ c = 2 ∨ c = 16 := by
  apply conwayAxisTensorOperator_eigenvalue p c T hT
  apply conwayTensorEmbedding_injective
  rw [← conwayAxis_tensor_product, map_smul]
  exact hc

/-- The axial linearization on the tensor block. -/
noncomputable def conwayAxisTensorLinearization (p : Fin 276) : Module.End ℝ ConwayTensorSpace :=
  (64 : ℝ) • (1 : Module.End ℝ ConwayTensorSpace) - (2 : ℝ) • conwayAxisTensorOperator p

/-- The tensor block has no eigenvalue 32, so its axial linearization is injective. -/
theorem conwayAxisTensorLinearization_injective (p : Fin 276) :
    Function.Injective (conwayAxisTensorLinearization p) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro T hT
  by_contra h
  have he : conwayAxisTensorOperator p T = (32 : ℝ) • T := by
    funext t i
    have hc := congrFun (congrFun hT t) i
    change 64 * T t i - 2 * conwayAxisTensorOperator p T t i = 0 at hc
    change conwayAxisTensorOperator p T t i = 32 * T t i
    linarith
  rcases conwayAxisTensorOperator_eigenvalue p 32 T h he with hc | (hc | hc) <;> norm_num at hc

/-- The tensor part of the axial linearization is a genuine linear equivalence. -/
noncomputable def conwayAxisTensorLinearizationEquiv (p : Fin 276) :
    ConwayTensorSpace ≃ₗ[ℝ] ConwayTensorSpace :=
  LinearEquiv.ofBijective (conwayAxisTensorLinearization p)
    ⟨conwayAxisTensorLinearization_injective p,
      LinearMap.injective_iff_surjective.mp (conwayAxisTensorLinearization_injective p)⟩

/-- The binary bases of the preferred short lifts label their actual lattice classes faithfully. -/
theorem griessShortQ_base_injective : Function.Injective (fun r => (griessShortQ r).base) := by
  intro r s h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact congrArg Multiplicative.toAdd h

/-- Preferred short lifts record addition of the actual binary lattice classes. -/
theorem griessShortQ_product_base_iff (r s u : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = (griessShortQ u).base ↔
      griessShortClass r + griessShortClass s = griessShortClass u := by
  constructor
  · intro h
    apply leechHyperbolicCoordinates.injective
    rw [map_add]
    exact congrArg Multiplicative.toAdd h
  · intro h
    apply Multiplicative.toAdd.injective
    change leechHyperbolicCoordinates (griessShortClass r) +
        leechHyperbolicCoordinates (griessShortClass s) =
      leechHyperbolicCoordinates (griessShortClass u)
    rw [← map_add, h]

private theorem qCentral_square (c : ZMod 2) : qCentral c * qCentral c = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact q_square_base _
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff]
    change c + c = 0
    exact ZModModule.add_self c

private theorem short_product_factor (r s u : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    griessShortQ r * griessShortQ s =
      qCentral (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) * griessShortQ u := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    exact h
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero]

private theorem involutive_phase_reverse {A : Type*} [Group A]
    (a b c z : A) (ha : a * a = 1) (hz : z * z = 1) (hza : z * a = a * z)
    (h : a * b = z * c) : a * c = z * b := by
  calc
    _ = z * (z * (a * c)) := by rw [← mul_assoc, hz, one_mul]
    _ = z * (a * (z * c)) := by
      congr 1
      rw [← mul_assoc, hza, mul_assoc]
    _ = z * (a * (a * b)) := by rw [← h]
    _ = z * b := by rw [← mul_assoc a, ha, one_mul]

/-- Left multiplication by an involutive preferred short lift reverses a short-class edge
with exactly the same central phase. -/
theorem short_product_reverse (r s u : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    griessShortQ r * griessShortQ u =
      qCentral (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) * griessShortQ s := by
  let C := qCentral (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff)
  have hC : C * C = 1 := qCentral_square _
  have hcomm : C * griessShortQ r = griessShortQ r * C := by
    apply (q_mul_comm_iff _ _).mpr
    change qBeta 0 _ = qBeta _ 0
    rw [qBeta_zero_left, qBeta_zero_right]
  have hf : griessShortQ r * griessShortQ s = C * griessShortQ u := short_product_factor r s u h
  exact involutive_phase_reverse (griessShortQ r) (griessShortQ s) (griessShortQ u) C
    (griessShortQ_square r) hC hcomm hf

/-- The short-class edge relation is symmetric. -/
theorem short_product_base_reverse (r s u : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    (griessShortQ r * griessShortQ u).base = (griessShortQ s).base := by
  rw [short_product_reverse r s u h, qCentral_mul_base]

/-- Reversing a short-class edge preserves the actual signed coefficient. -/
theorem short_product_phase_reverse (r s u : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) :
    Multiplicative.toAdd (griessShortQ r * griessShortQ u).coeff =
      Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff := by
  rw [short_product_reverse r s u h, qCentral_mul_coeff, griessShortQ_coeff, add_zero]

/-- Signed translation by a fixed short lift on the set of shortest-vector classes. -/
noncomputable def conwayShortTranslationMatrix (r : GriessShortIndex) :
    Matrix GriessShortIndex GriessShortIndex ℝ := fun u s =>
  if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
    qSign (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) else 0

noncomputable def conwayShortTranslation (r : GriessShortIndex) :
    Module.End ℝ (GriessShortIndex → ℝ) := (conwayShortTranslationMatrix r).mulVecLin

private theorem short_product_base_unique (r u s t : GriessShortIndex)
    (hs : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base)
    (ht : (griessShortQ r * griessShortQ t).base = (griessShortQ u).base) : s = t := by
  apply griessShortQ_base_injective
  apply mul_left_cancel (a := (griessShortQ r).base)
  exact hs.trans ht.symm

private theorem matrix_row_apply {I : Type*} [Fintype I]
    (M : Matrix I I ℝ) (X : I → ℝ) (u : I) :
    M.mulVecLin X u = ∑ s, M u s * X s := rfl

/-- Evaluate signed translation as its exact matrix row sum. -/
theorem conwayShortTranslation_apply (r u : GriessShortIndex) (X : GriessShortIndex → ℝ) :
    conwayShortTranslation r X u = ∑ s, conwayShortTranslationMatrix r u s * X s :=
  matrix_row_apply _ _ _

/-- Each translated coordinate is exactly its unique neighboring coordinate with its phase. -/
theorem conwayShortTranslation_apply_edge (r u s : GriessShortIndex)
    (h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base)
    (X : GriessShortIndex → ℝ) :
    conwayShortTranslation r X u =
      qSign (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) * X s := by
  rw [conwayShortTranslation_apply]
  rw [Finset.sum_eq_single s]
  · rw [conwayShortTranslationMatrix, ite_eq_left h]
  · intro t _ hts
    have hn : ¬(griessShortQ r * griessShortQ t).base = (griessShortQ u).base := by
      intro ht
      exact hts (short_product_base_unique r u t s ht h)
    rw [conwayShortTranslationMatrix, ite_eq_right hn, zero_mul]
  · simp

/-- A class having no short neighbor is killed by the partial translation. -/
theorem conwayShortTranslation_apply_no_edge (r u : GriessShortIndex)
    (h : ¬∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base)
    (X : GriessShortIndex → ℝ) : conwayShortTranslation r X u = 0 := by
  rw [conwayShortTranslation_apply]
  apply Finset.sum_eq_zero
  intro s _
  rw [conwayShortTranslationMatrix, ite_eq_right (fun hs => h ⟨s, hs⟩), zero_mul]

/-- Two signed translations give identity on neighboring short classes and zero on all others. -/
theorem conwayShortTranslation_square_apply (r u : GriessShortIndex) (X : GriessShortIndex → ℝ) :
    conwayShortTranslation r (conwayShortTranslation r X) u =
      if ∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then X u else 0 := by
  classical
  by_cases h : ∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · rw [ite_eq_left h]
    obtain ⟨s, hs⟩ := h
    rw [conwayShortTranslation_apply_edge r u s hs,
      conwayShortTranslation_apply_edge r s u (short_product_base_reverse r s u hs),
      short_product_phase_reverse r s u hs, ← mul_assoc, qSign_sq, one_mul]
  · rw [ite_eq_right h, conwayShortTranslation_apply_no_edge r u h]

/-- The signed partial translation matrix is symmetric, including its actual central phases. -/
theorem conwayShortTranslationMatrix_symmetric (r u s : GriessShortIndex) :
    conwayShortTranslationMatrix r u s = conwayShortTranslationMatrix r s u := by
  classical
  by_cases h : (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · rw [conwayShortTranslationMatrix, conwayShortTranslationMatrix, ite_eq_left h,
      ite_eq_left (short_product_base_reverse r s u h), short_product_phase_reverse r s u h]
  · have hn : ¬(griessShortQ r * griessShortQ u).base = (griessShortQ s).base := by
      intro hs
      exact h (short_product_base_reverse r u s hs)
    rw [conwayShortTranslationMatrix, conwayShortTranslationMatrix,
      ite_eq_right h, ite_eq_right hn]

/-- A translated coordinate has a short neighbor exactly when the binary sum is a short class. -/
theorem short_product_edge_iff_short_class (r u : GriessShortIndex) :
    (∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) ↔
      IsLeechShortClass (griessShortClass r + griessShortClass u) := by
  constructor
  · rintro ⟨s, hs⟩
    have he := (griessShortQ_product_base_iff r u s).mp (short_product_base_reverse r s u hs)
    rw [he]
    exact (griessShortClassMap s).property
  · intro h
    obtain ⟨s, hs⟩ := griessShortClassEquiv.surjective ⟨_, h⟩
    have he : griessShortClass s = griessShortClass r + griessShortClass u :=
      congrArg Subtype.val hs
    have hb := (griessShortQ_product_base_iff r u s).mpr he.symm
    exact ⟨s, short_product_base_reverse r u s hb⟩

/-- Signed translation supports precisely the short classes with axial pairing ±2. -/
theorem short_product_edge_iff_pairing (r u : GriessShortIndex) :
    (∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base) ↔
      stdPairingFun (griessShortVector r) (griessShortVector u) = 2 ∨
        stdPairingFun (griessShortVector r) (griessShortVector u) = -2 := by
  rw [short_product_edge_iff_short_class, griessShort_sum_class_iff_real_pairing]

/-- No shortest class is a neighbor of the translating class itself. -/
theorem short_product_self_no_edge (r : GriessShortIndex) :
    ¬∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ r).base := by
  rintro ⟨s, hs⟩
  apply griessShortQ_base_ne_one s
  apply mul_left_cancel (a := (griessShortQ r).base)
  change (griessShortQ r).base * (griessShortQ s).base = (griessShortQ r).base at hs
  simpa only [mul_one] using hs

/-- The translating coordinate is killed by the signed partial translation. -/
theorem conwayShortTranslation_self (r : GriessShortIndex) (X : GriessShortIndex → ℝ) :
    conwayShortTranslation r X r = 0 :=
  conwayShortTranslation_apply_no_edge r r (short_product_self_no_edge r) X

set_option maxHeartbeats 1000000 in
-- Keep the finite coordinate types opaque during the signed edge argument.
/-- Outside the translating coordinate, the actual signed-translation/diagonal block
has no eigenvector of eigenvalue 32. -/
theorem conwayShort_off_axis_32_kernel (r : GriessShortIndex) (X : GriessShortIndex → ℝ)
    (hX : ∀ u, u ≠ r →
      2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 * X u -
        8 * conwayShortTranslation r X u = 32 * X u) :
    ∀ u, u ≠ r → X u = 0 := by
  intro u hur
  classical
  by_cases he : ∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
  · obtain ⟨s, hs⟩ := he
    have hsrev := short_product_base_reverse r s u hs
    have hsr : s ≠ r := by
      intro hsr
      subst s
      exact short_product_self_no_edge r ⟨u, hsrev⟩
    have huD : 2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 = 8 := by
      rcases (short_product_edge_iff_pairing r u).mp ⟨s, hs⟩ with h | h <;>
        rw [h] <;> norm_num
    have hsD : 2 * stdPairingFun (griessShortVector r) (griessShortVector s) ^ 2 = 8 := by
      rcases (short_product_edge_iff_pairing r s).mp ⟨u, hsrev⟩ with h | h <;>
        rw [h] <;> norm_num
    have hu := hX u hur
    have hsu := hX s hsr
    rw [huD, conwayShortTranslation_apply_edge r u s hs] at hu
    rw [hsD, conwayShortTranslation_apply_edge r s u hsrev,
      short_product_phase_reverse r s u hs] at hsu
    by_cases hc : Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff = 0
    · simp only [qSign, ite_eq_left hc, one_mul] at hu hsu
      linarith
    · simp only [qSign, ite_eq_right hc, neg_mul, one_mul] at hu hsu
      linarith
  · have hu := hX u hur
    rw [conwayShortTranslation_apply_no_edge r u he] at hu
    have hb := griessShort_pairing_bounds r u (Ne.symm hur)
    have hsq : stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 ≤ 4 := by
      have hp := mul_nonneg
        (show 0 ≤ stdPairingFun (griessShortVector r) (griessShortVector u) + 2 by linarith)
        (show 0 ≤ 2 - stdPairingFun (griessShortVector r) (griessShortVector u) by linarith)
      nlinarith
    have hz :
        (2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 - 32) * X u = 0 := by
      nlinarith [hu]
    exact (mul_eq_zero.mp hz).resolve_left (by linarith)

/-- The preferred lifts multiply to the central coset exactly for equal short labels. -/
theorem conwayAxisShort_product_base_one_iff (r s : GriessShortIndex) :
    (griessShortQ r * griessShortQ s).base = 1 ↔ s = r := by
  have hrr : (griessShortQ r).base * (griessShortQ r).base = 1 :=
    q_square_base (griessShortQ r)
  constructor
  · intro h
    apply griessShortQ_base_injective
    apply mul_left_cancel (a := (griessShortQ r).base)
    change (griessShortQ r).base * (griessShortQ s).base = 1 at h
    exact h.trans hrr.symm
  · rintro rfl
    exact hrr

private theorem outer_pairing {I : Type*} [Fintype I] (v w : I → ℝ) :
    (∑ i, ∑ j, (2 * (v i * v j)) * w i * w j) =
      2 * (∑ i, v i * w i) ^ 2 := by
  have he (i j : I) : (2 * (v i * v j)) * w i * w j =
      (2 * (v i * w i)) * (v j * w j) := by ring
  simp_rw [he, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The short-axis matrix acts on short coordinates by twice their axial pairing squared. -/
theorem conwayShortAxis_matrix_pairing (r u : GriessShortIndex) :
    conwayShortPairing ((2 : ℝ) •
      Matrix.vecMulVec (griessShortVector r) (griessShortVector r)) u =
      2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 := by
  unfold conwayShortPairing stdPairingFun
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  exact outer_pairing (I := Fin 24) (griessShortVector r) (griessShortVector u)

private theorem short_axis_short_contraction (r u : GriessShortIndex) (a : ℝ)
    (X : GriessShortIndex → ℝ) :
    (∑ v, ∑ s, if (griessShortQ v * griessShortQ s).base = (griessShortQ u).base then
      qSign (Multiplicative.toAdd (griessShortQ v * griessShortQ s).coeff) *
        (a • Pi.single r 1) v * X s else 0) = a * conwayShortTranslation r X u := by
  classical
  rw [Finset.sum_eq_single r]
  · rw [conwayShortTranslation_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      conwayShortTranslationMatrix]
    split_ifs <;> ring
  · intro v _ hvr
    simp [Pi.single_eq_of_ne hvr]
  · simp

private theorem short_axis_matrix_contraction (r : GriessShortIndex) (a : ℝ)
    (X : GriessShortIndex → ℝ) (i j : Fin 24) :
    (∑ v, ∑ s, if (griessShortQ v * griessShortQ s).base = 1 then
      qSign (Multiplicative.toAdd (griessShortQ v * griessShortQ s).coeff) *
        (a • Pi.single r 1) v * X s * griessShortVector v i * griessShortVector v j else 0) =
      a * X r * griessShortVector r i * griessShortVector r j := by
  classical
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single r]
    · rw [griessShortQ_square]
      change (if True then qSign 0 * (a • Pi.single r 1) r * X r * _ * _ else 0) = _
      simp only [ite_true, qSign_zero, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one, one_mul]
    · intro s _ hsr
      rw [ite_eq_right (fun h => hsr ((conwayAxisShort_product_base_one_iff r s).mp h))]
    · simp
  · intro v _ hvr
    simp [Pi.single_eq_of_ne hvr]
  · simp

/-- The exact short-coordinate row of multiplication by a signed short axis. -/
theorem conwayShortAxisRaw_product_short (r u : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) :
    (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).2.1 u =
      2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 * X u +
        conwayShortPairing M u * ((-8 * qSign c) • Pi.single r 1) u +
        (-8 * qSign c) * conwayShortTranslation r X u := by
  dsimp only [conwayRawProduct, conwayShortAxisRaw]
  rw [conwayShortAxis_matrix_pairing, short_axis_short_contraction]
  simp [spinOperator]

private theorem rank_one_matrix_product {I : Type*} [Fintype I]
    (v : I → ℝ) (M : Matrix I I ℝ) (i j : I) :
    2 * (∑ k, ((2 * (v i * v k)) * M k j + M i k * (2 * (v k * v j)))) =
      4 * (v i * (∑ k, v k * M k j) + (∑ k, M i k * v k) * v j) := by
  have he (k : I) : ((2 * (v i * v k)) * M k j + M i k * (2 * (v k * v j))) =
      (2 * v i) * (v k * M k j) + (2 * v j) * (M i k * v k) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The exact symmetric-matrix row of multiplication by a signed short axis. -/
theorem conwayShortAxisRaw_product_matrix (r : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) (i j : Fin 24) :
    (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).1 i j =
      4 * (griessShortVector r i * (∑ k, griessShortVector r k * M k j) +
        (∑ k, M i k * griessShortVector r k) * griessShortVector r j) -
        (8 * qSign c) * X r * griessShortVector r i * griessShortVector r j := by
  dsimp only [conwayRawProduct, conwayShortAxisRaw]
  rw [short_axis_matrix_contraction]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Pi.zero_apply, zero_mul, mul_zero, add_zero, Finset.sum_const_zero, zero_div]
  rw [rank_one_matrix_product (I := Fin 24) (griessShortVector r) M i j]
  ring

/-- The signed version of the off-axis short-coordinate midpoint exclusion. -/
theorem conwayShort_signed_off_axis_32_kernel (r : GriessShortIndex) (c : ZMod 2)
    (X : GriessShortIndex → ℝ)
    (hX : ∀ u, u ≠ r →
      2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 * X u -
        8 * qSign c * conwayShortTranslation r X u = 32 * X u) :
    ∀ u, u ≠ r → X u = 0 := by
  classical
  by_cases hc : c = 0
  · apply conwayShort_off_axis_32_kernel r X
    intro u hu
    simpa only [hc, qSign_zero, mul_one] using hX u hu
  · intro u hur
    by_cases he : ∃ s, (griessShortQ r * griessShortQ s).base = (griessShortQ u).base
    · obtain ⟨s, hs⟩ := he
      have hsrev := short_product_base_reverse r s u hs
      have hsr : s ≠ r := by
        intro hsr
        subst s
        exact short_product_self_no_edge r ⟨u, hsrev⟩
      have huD : 2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 = 8 := by
        rcases (short_product_edge_iff_pairing r u).mp ⟨s, hs⟩ with h | h <;>
          rw [h] <;> norm_num
      have hsD : 2 * stdPairingFun (griessShortVector r) (griessShortVector s) ^ 2 = 8 := by
        rcases (short_product_edge_iff_pairing r s).mp ⟨u, hsrev⟩ with h | h <;>
          rw [h] <;> norm_num
      have hu := hX u hur
      have hsu := hX s hsr
      rw [huD, conwayShortTranslation_apply_edge r u s hs] at hu
      rw [hsD, conwayShortTranslation_apply_edge r s u hsrev,
        short_product_phase_reverse r s u hs] at hsu
      by_cases hphase : Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff = 0
      · simp only [qSign, ite_eq_right hc, ite_eq_left hphase, neg_mul, mul_neg,
          mul_one, one_mul] at hu hsu
        linarith
      · simp only [qSign, ite_eq_right hc, ite_eq_right hphase, neg_mul, mul_neg,
          mul_one, one_mul] at hu hsu
        linarith
    · have hu := hX u hur
      rw [conwayShortTranslation_apply_no_edge r u he] at hu
      have hb := griessShort_pairing_bounds r u (Ne.symm hur)
      have hsq : stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 ≤ 4 := by
        have hp := mul_nonneg
          (show 0 ≤ stdPairingFun (griessShortVector r) (griessShortVector u) + 2 by linarith)
          (show 0 ≤ 2 - stdPairingFun (griessShortVector r) (griessShortVector u) by linarith)
        nlinarith
      have hz :
          (2 * stdPairingFun (griessShortVector r) (griessShortVector u) ^ 2 - 32) * X u = 0 := by
        nlinarith [hu]
      exact (mul_eq_zero.mp hz).resolve_left (by linarith)

private theorem qSign_ne_zero (c : ZMod 2) : qSign c ≠ 0 := by
  intro h
  have hs := qSign_sq c
  rw [h, zero_mul] at hs
  norm_num at hs

/-- Every short vector pairs with itself to four in the genuine physical coordinates. -/
theorem griessShortVector_self_pairing (r : GriessShortIndex) :
    stdPairingFun (griessShortVector r) (griessShortVector r) = 4 :=
  griessShortVector_norm_sq r

/-- Multiplication by any signed short axis has trivial midpoint kernel
on its symmetric-matrix and short-coordinate blocks. -/
theorem conwayShortAxisRaw_matrix_short_32_kernel (r : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) (hsym : ∀ i j, M i j = M j i)
    (hM : ∀ i j, (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).1 i j = 32 * M i j)
    (hX : ∀ u, (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).2.1 u = 32 * X u) :
    M = 0 ∧ X = 0 := by
  classical
  have hoff : ∀ u, u ≠ r → X u = 0 := by
    apply conwayShort_signed_off_axis_32_kernel r c X
    intro u hur
    have hu := hX u
    rw [conwayShortAxisRaw_product_short] at hu
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hur, smul_eq_mul,
      mul_zero, add_zero] at hu
    nlinarith [hu]
  have hpair : conwayShortPairing M r = 0 := by
    have hr := hX r
    rw [conwayShortAxisRaw_product_short, griessShortVector_self_pairing,
      conwayShortTranslation_self] at hr
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      mul_zero, add_zero] at hr
    have hz : conwayShortPairing M r * qSign c = 0 := by nlinarith [hr]
    exact (mul_eq_zero.mp hz).resolve_right (qSign_ne_zero c)
  have hcontract : (∑ i, ∑ j, griessShortVector r i * M i j * griessShortVector r j) = 0 := by
    rw [← hpair]
    unfold conwayShortPairing
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq (i j : Fin 24) :
      4 * (griessShortVector r i * (∑ k, griessShortVector r k * M k j) +
        (∑ k, M i k * griessShortVector r k) * griessShortVector r j) -
        (8 * qSign c) * X r * griessShortVector r i * griessShortVector r j =
        2 * 4 * 4 * M i j := by
    rw [← conwayShortAxisRaw_product_matrix]
    convert hM i j using 1; ring
  have hβ : (8 : ℝ) * qSign c ≠ 0 := mul_ne_zero (by norm_num) (qSign_ne_zero c)
  obtain ⟨hxr, hm⟩ := matrix_axis_midpoint_kernel (griessShortVector r) M (X r)
    4 4 (8 * qSign c) (by norm_num) (by norm_num) hβ
    (griessShortVector_norm_sq r) hsym hcontract heq
  refine ⟨hm, ?_⟩
  funext u
  by_cases hur : u = r
  · simpa only [hur, Pi.zero_apply] using hxr
  · exact hoff u hur

/-- Spin involution associated to the axis's preferred norm-four short lift. -/
noncomputable def conwayShortSpin (r : GriessShortIndex) : Module.End ℝ ConwayTensorSpace where
  toFun T t i := spinOperator (griessShortQ r) (fun u => T u i) t
  map_add' T U := by
    funext t i
    exact congrFun ((spinOperator _).map_add (fun u => T u i) (fun u => U u i)) t
  map_smul' c T := by
    funext t i
    exact congrFun ((spinOperator _).map_smul c (fun u => T u i)) t

/-- Orthogonal spatial projection onto the coordinate difference underlying the axis. -/
noncomputable def conwayShortTensorProjection (r : GriessShortIndex) :
    Module.End ℝ ConwayTensorSpace where
  toFun T t i := (∑ j, T t j * griessShortVector r j) * griessShortVector r i / 4
  map_add' T U := by
    funext t i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]
  map_smul' c T := by
    funext t i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc c]
    rw [← Finset.mul_sum]
    ring

/-- The spin factor is a genuine involution, using the proven square of the short lift. -/
theorem conwayShortSpin_square (r : GriessShortIndex) :
    conwayShortSpin r * conwayShortSpin r = 1 := by
  apply LinearMap.ext
  intro T
  funext t i
  have h := congrArg (fun F : SpinSpace →ₗ[ℝ] SpinSpace => F (fun u => T u i) t)
    (spinOperator_mul (griessShortQ r) (griessShortQ r))
  rw [griessShortQ_square, spinOperator_one] at h
  exact h.symm

/-- The spatial factor is a genuine rank-one projection. -/
theorem conwayShortTensorProjection_square (r : GriessShortIndex) :
    conwayShortTensorProjection r * conwayShortTensorProjection r =
      conwayShortTensorProjection r := by
  apply LinearMap.ext
  intro T
  funext t i
  change (∑ j, ((∑ k, T t k * griessShortVector r k) *
      griessShortVector r j / 4) *
      griessShortVector r j) * griessShortVector r i / 4 = _
  have he (j : Fin 24) :
      ((∑ k, T t k * griessShortVector r k) * griessShortVector r j / 4) *
        griessShortVector r j =
      ((∑ k, T t k * griessShortVector r k) / 4) *
        (griessShortVector r j * griessShortVector r j) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, griessShortVector_norm_sq]
  change _ = (∑ k, T t k * griessShortVector r k) * griessShortVector r i / 4
  ring

/-- Spin and spatial projection operate on different tensor factors and commute. -/
theorem conwayShortSpin_projection_commute (r : GriessShortIndex) :
    conwayShortSpin r * conwayShortTensorProjection r =
      conwayShortTensorProjection r * conwayShortSpin r := by
  apply LinearMap.ext
  intro T
  funext t i
  simp only [Module.End.mul_apply, conwayShortSpin, conwayShortTensorProjection,
    LinearMap.coe_mk, AddHom.coe_mk, spinOperator]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- The spin involution with the actual signed short-axis phase. -/
noncomputable def conwayShortAxisSignedSpin (r : GriessShortIndex) (c : ZMod 2) :
    Module.End ℝ ConwayTensorSpace := qSign c • conwayShortSpin r

/-- Changing the central phase retains the spin involution. -/
theorem conwayShortAxisSignedSpin_square (r : GriessShortIndex) (c : ZMod 2) :
    conwayShortAxisSignedSpin r c * conwayShortAxisSignedSpin r c = 1 := by
  simp only [conwayShortAxisSignedSpin, smul_mul_assoc, mul_smul_comm,
    smul_smul, conwayShortSpin_square, qSign_sq, one_smul]

/-- The signed spin factor commutes with the short spatial projection. -/
theorem conwayShortAxisSignedSpin_projection_commute (r : GriessShortIndex) (c : ZMod 2) :
    conwayShortAxisSignedSpin r c * conwayShortTensorProjection r =
      conwayShortTensorProjection r * conwayShortAxisSignedSpin r c := by
  simp only [conwayShortAxisSignedSpin, smul_mul_assoc, mul_smul_comm,
    conwayShortSpin_projection_commute]

/-- The source-normalized tensor operator for every signed short axis. -/
noncomputable def conwayShortAxisTensorOperator (r : GriessShortIndex) (c : ZMod 2) :
    Module.End ℝ ConwayTensorSpace :=
  1 - conwayShortAxisSignedSpin r c + 8 * conwayShortTensorProjection r +
    8 * (conwayShortAxisSignedSpin r c * conwayShortTensorProjection r)

/-- Every signed-short tensor block has the source annihilator with roots zero, two, and sixteen. -/
theorem conwayShortAxisTensorOperator_polynomial (r : GriessShortIndex) (c : ZMod 2) :
    conwayShortAxisTensorOperator r c * (conwayShortAxisTensorOperator r c - 2) *
      (conwayShortAxisTensorOperator r c - 16) = 0 :=
  involution_projection_polynomial (conwayShortAxisSignedSpin r c) (conwayShortTensorProjection r)
    (conwayShortAxisSignedSpin_square r c) (conwayShortTensorProjection_square r)
    (conwayShortAxisSignedSpin_projection_commute r c)

/-- The coordinate action of every signed-short tensor operator. -/
theorem conwayShortAxisTensorOperator_apply (r : GriessShortIndex) (c : ZMod 2)
    (T : ConwayTensorSpace) (t : SpinIndex) (i : Fin 24) :
    conwayShortAxisTensorOperator r c T t i =
      T t i - conwayShortAxisSignedSpin r c T t i +
      2 * (∑ j, T t j * griessShortVector r j) * griessShortVector r i +
      2 * (∑ j, conwayShortAxisSignedSpin r c T t j * griessShortVector r j) *
        griessShortVector r i := by
  have hc := congrArg (fun L : Module.End ℝ ConwayTensorSpace => L T t i)
    (conwayShortAxisSignedSpin_projection_commute r c)
  simp only [Module.End.mul_apply] at hc
  simp only [conwayShortAxisTensorOperator, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, Module.End.mul_apply, Module.End.ofNat_apply,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.ofNat_apply]
  rw [hc]
  change T t i - conwayShortAxisSignedSpin r c T t i +
      8 * ((∑ j, T t j * griessShortVector r j) * griessShortVector r i / 4) +
      8 * ((∑ j, conwayShortAxisSignedSpin r c T t j * griessShortVector r j) *
        griessShortVector r i / 4) = _
  ring

/-- The tensor block has no eigenvalues besides the three source values. -/
theorem conwayShortAxisTensorOperator_eigenvalue (r : GriessShortIndex)
    (phase : ZMod 2) (c : ℝ) (T : ConwayTensorSpace)
    (hT : T ≠ 0) (hc : conwayShortAxisTensorOperator r phase T = c • T) :
    c = 0 ∨ c = 2 ∨ c = 16 := by
  have hp := congrArg (fun L : Module.End ℝ ConwayTensorSpace => L T)
    (conwayShortAxisTensorOperator_polynomial r phase)
  have h2 : (conwayShortAxisTensorOperator r phase - 2) T = (c - 2) • T := by
    simp only [LinearMap.sub_apply, hc, Module.End.ofNat_apply]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    change c • T - (2 : ℝ) • T = (c - 2) • T
    rw [sub_smul]
  have h16 : (conwayShortAxisTensorOperator r phase - 16) T = (c - 16) • T := by
    simp only [LinearMap.sub_apply, hc, Module.End.ofNat_apply]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    change c • T - (16 : ℝ) • T = (c - 16) • T
    rw [sub_smul]
  rw [Module.End.mul_apply, Module.End.mul_apply, h16, map_smul, h2] at hp
  simp only [map_smul, hc, smul_smul] at hp
  simp only [LinearMap.zero_apply] at hp
  rw [mul_assoc] at hp
  change ((c - 16) * ((c - 2) * c)) • T = 0 at hp
  have hz : (c - 16) * ((c - 2) * c) = 0 := (smul_eq_zero.mp hp).resolve_right hT
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inl h

/-- No signed-short tensor midpoint eigenvector exists. -/
theorem conwayShortAxisTensorOperator_32_kernel (r : GriessShortIndex) (c : ZMod 2)
    (T : ConwayTensorSpace) (hT : conwayShortAxisTensorOperator r c T = (32 : ℝ) • T) :
    T = 0 := by
  by_contra h
  have he := conwayShortAxisTensorOperator_eigenvalue r c 32 T h hT
  rcases he with h | h | h <;> norm_num at h

private theorem shortAxis_matrix_trace (r : GriessShortIndex) :
    Matrix.trace ((2 : ℝ) • Matrix.vecMulVec (griessShortVector r) (griessShortVector r)) = 8 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [← Finset.mul_sum, griessShortVector_norm_sq]
  norm_num

/-- The exact tensor row of multiplication by every signed short axis. -/
theorem conwayShortAxisRaw_product_tensor (r : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) :
    (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).2.2 =
      conwayShortAxisTensorOperator r c T := by
  let S : GriessShortIndex → ℝ := (-8 * qSign c : ℝ) • Pi.single r 1
  have hs0 : S r = -8 * qSign c := by simp [S]
  have hs (u : GriessShortIndex) (hur : u ≠ r) : S u = 0 := by simp [S, hur]
  have hmat (t : SpinIndex) (i : Fin 24) :
      (∑ j, ((2 : ℝ) • Matrix.vecMulVec (griessShortVector r)
          (griessShortVector r)) j i * T t j) =
        2 * (∑ j, T t j * griessShortVector r j) * griessShortVector r i := by
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    have he (j : Fin 24) : 2 * (griessShortVector r j * griessShortVector r i) * T t j =
        (2 * griessShortVector r i) * (T t j * griessShortVector r j) := by ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    ring
  have hxt (t : SpinIndex) (i : Fin 24) :
      (∑ u, ∑ j, S u * spinOperator (griessShortQ u) (fun v => T v j) t *
        conwayTensorCoefficient u j i) =
      -8 * (conwayShortAxisSignedSpin r c T t i -
        2 * (∑ j, conwayShortAxisSignedSpin r c T t j * griessShortVector r j) *
          griessShortVector r i) := by
    rw [Finset.sum_eq_single r]
    · rw [hs0]
      change (∑ j, (-8 * qSign c) * conwayShortSpin r T t j *
          ((if j = i then 1 else 0) - 2 * griessShortVector r j * griessShortVector r i)) = _
      simp only [conwayShortAxisSignedSpin, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      have he (j : Fin 24) :
          (-8 * qSign c) * conwayShortSpin r T t j *
            ((if j = i then 1 else 0) - 2 * griessShortVector r j * griessShortVector r i) =
          -8 * (qSign c * conwayShortSpin r T t j * (if j = i then 1 else 0) -
            (2 * griessShortVector r i) *
              (qSign c * conwayShortSpin r T t j * griessShortVector r j)) := by ring
      simp_rw [he]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    · intro u _ hur
      simp [hs u hur]
    · simp
  funext t i
  change (conwayRawProduct
    (((2 : ℝ) • Matrix.vecMulVec (griessShortVector r) (griessShortVector r)), (S, 0))
      (M, (X, T))).2.2 t i = _
  dsimp only [conwayRawProduct]
  have hzero (u : GriessShortIndex) :
      spinOperator (griessShortQ u) (fun _ : SpinIndex => (0 : ℝ)) t = 0 :=
    congrFun ((spinOperator (griessShortQ u)).map_zero) t
  simp only [Pi.zero_apply, hzero, mul_zero, add_zero]
  rw [hmat, shortAxis_matrix_trace]
  change _ + 8 / 8 * T t i + _ / 8 = _
  rw [hxt, conwayShortAxisTensorOperator_apply]
  ring

/-- The full raw signed-short axis has no midpoint eigenvector. -/
theorem conwayShortAxisRaw_32_kernel (r : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) (hsym : ∀ i j, M i j = M j i)
    (h : conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T)) =
      (32 : ℝ) • (M, (X, T))) : (M, (X, T)) = (0 : ConwayRawSpace) := by
  have hM (i j : Fin 24) := congrArg (fun z : ConwayRawSpace => z.1 i j) h
  have hX (u : GriessShortIndex) := congrArg (fun z : ConwayRawSpace => z.2.1 u) h
  obtain ⟨hm, hx⟩ := conwayShortAxisRaw_matrix_short_32_kernel r c M X T hsym hM hX
  have ht := congrArg (fun z : ConwayRawSpace => z.2.2) h
  rw [conwayShortAxisRaw_product_tensor] at ht
  have ht0 := conwayShortAxisTensorOperator_32_kernel r c T ht
  simp only [hm, hx, ht0, Prod.zero_eq_mk]

/-- Actual Griess multiplication by every signed-short axis has no midpoint eigenvector. -/
theorem conwayShortAxis_32_kernel (r : GriessShortIndex) (c : ZMod 2) (x : GriessSpace)
    (h : griessProd (conwayShortAxis r c) x = (32 : ℝ) • x) : x = 0 := by
  have he : conwayRawProduct (conwayShortAxisRaw r c) (griessConwayEncode x) =
      (32 : ℝ) • griessConwayEncode x := by
    have hh := congrArg griessConwayEncode h
    rw [griessProd_encode, conwayShortAxis_encode] at hh
    have hsm : griessConwayEncode ((32 : ℝ) • x) = (32 : ℝ) • griessConwayEncode x :=
      griessConwayEncodeLinear.map_smul 32 x
    rw [hsm] at hh
    exact hh
  have hz := conwayShortAxisRaw_32_kernel r c (griessConwayEncode x).1
    (griessConwayEncode x).2.1 (griessConwayEncode x).2.2 (griessConwayEncode_symmetric x) he
  have hd := congrArg griessConwayDecode hz
  change griessConwayDecode (griessConwayEncode x) = griessConwayDecode 0 at hd
  rw [griessConwayDecode_encode] at hd
  simpa only [show griessConwayDecode (0 : ConwayRawSpace) = 0 from
    griessConwayDecodeLinear.map_zero] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
