/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.NetworkGrowth
public import CSLibExt.MachineLearning.PACLearning.HalfspaceVCDim

/-!
# Growth bound for sign-activation networks

The network growth lemma behind Shalev-Shwartz and Ben-David,
*Understanding Machine Learning: From Theory to Algorithms*,
Theorem 20.6: for a fixed architecture of affine-threshold
neurons, the growth function of the network class is at most the
product of the per-neuron Sauer bounds, hence at most
`(e * m) ^ E` where `E` counts weights and biases. Layers are
adjacent only. A hidden neuron on Boolean inputs is a halfspace
precomposed with the `{0, 1}` embedding of the Boolean cube into
Euclidean space.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- The `{0, 1}` embedding of the Boolean cube into Euclidean space. -/
noncomputable def boolEmbed (k : ℕ) : (Fin k → Bool) → EuclideanSpace ℝ (Fin k) :=
  fun y => (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => if y i then (1 : ℝ) else 0)

/-- The Boolean-cube embedding is injective. -/
theorem boolEmbed_injective (k : ℕ) : Function.Injective (boolEmbed k) := by
  intro y₁ y₂ h
  have h2 := congrArg (WithLp.equiv 2 (Fin k → ℝ)) h
  simp only [boolEmbed, Equiv.apply_symm_apply] at h2
  funext i
  have hi := congrFun h2 i
  cases hy1 : y₁ i <;> cases hy2 : y₂ i
  · rfl
  · simp [hy1, hy2] at hi
  · simp [hy1, hy2] at hi
  · rfl

/-- A threshold neuron on Boolean inputs: a halfspace precomposed
with the Boolean-cube embedding. -/
noncomputable def neuronClass (k : ℕ) : ConceptClass (Fin k → Bool) Bool :=
  precompClass (boolEmbed k) (halfspaceClass k)

/-- Neuron growth is at most halfspace growth at the same fan-in. -/
theorem growthFunctionVec_neuronClass_le (k m : ℕ) :
    growthFunctionVec (neuronClass k) m ≤
      growthFunctionVec (halfspaceClass k) m := by
  unfold neuronClass
  exact growthFunctionVec_precomp_le (boolEmbed_injective k) _ _

/-- Per-neuron Sauer bound at any capped sample size `j ≤ m`, as a
real inequality with the bound taken at `m`. -/
theorem growthFunctionVec_halfspaceClass_le_real (f j m : ℕ)
    (hjm : j ≤ m) (hf : f + 1 ≤ m) :
    (growthFunctionVec (halfspaceClass f) j : ℝ) ≤
      (Real.exp 1 * (m : ℝ) / (f + 1 : ℕ)) ^ (f + 1) := by
  by_cases hcase : f + 1 ≤ j
  · have hvc : vcDim (halfspaceClass f) = f + 1 := halfspaceClass_vcDim f
    have hd : 1 ≤ vcDim (halfspaceClass f) := by
      rw [hvc]
      omega
    have hdm : vcDim (halfspaceClass f) ≤ j := by
      rw [hvc]
      exact hcase
    have hsauer := growthFunction_le_exp_pow (halfspaceClass f) j
      (halfspaceClass_hasFiniteVCDim f) hd hdm
    rw [hvc] at hsauer
    have hbridge : (growthFunctionVec (halfspaceClass f) j : ℝ) =
        (growthFunction (halfspaceClass f) j : ℝ) := by
      exact_mod_cast growthFunctionVec_bool_eq (halfspaceClass f) j
    rw [hbridge]
    have hfpos : (0 : ℝ) < ((f + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos f
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hbase_nonneg :
        (0 : ℝ) ≤ Real.exp 1 * (j : ℝ) / ((f + 1 : ℕ) : ℝ) := by
      apply div_nonneg
      · exact mul_nonneg (le_of_lt he_pos) (Nat.cast_nonneg j)
      · exact Nat.cast_nonneg (f + 1)
    have hjm' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
    have hmul : Real.exp 1 * (j : ℝ) ≤ Real.exp 1 * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hjm' (le_of_lt he_pos)
    have hbase_le : Real.exp 1 * (j : ℝ) / ((f + 1 : ℕ) : ℝ) ≤
        Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ) :=
      (div_le_div_iff_of_pos_right hfpos).mpr hmul
    calc ((growthFunction (halfspaceClass f) j : ℕ) : ℝ)
        ≤ (Real.exp 1 * (j : ℝ) / ((f + 1 : ℕ) : ℝ)) ^ (f + 1) := hsauer
      _ ≤ (Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ)) ^ (f + 1) :=
          pow_le_pow_left₀ hbase_nonneg hbase_le _
  · have hlt : j < f + 1 := not_le.mp hcase
    have htriv := growthFunctionVec_le_pow (halfspaceClass f) j
    have htriv2 : growthFunctionVec (halfspaceClass f) j ≤ 2 ^ j := by
      simpa [Fintype.card_bool] using htriv
    have hcast : ((growthFunctionVec (halfspaceClass f) j : ℕ) : ℝ) ≤
        ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast htriv2
    rw [Nat.cast_pow, Nat.cast_two] at hcast
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h
      linarith
    have he_nonneg : (0 : ℝ) ≤ Real.exp 1 := by linarith
    have hfpos : (0 : ℝ) < ((f + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos f
    have h1le : (1 : ℝ) ≤ (m : ℝ) / ((f + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hfpos]
      calc (1 : ℝ) * ((f + 1 : ℕ) : ℝ) = ((f + 1 : ℕ) : ℝ) := one_mul _
        _ ≤ (m : ℝ) := by exact_mod_cast hf
    have he_le : Real.exp 1 ≤ Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ) := by
      have hmul : Real.exp 1 * 1 ≤
          Real.exp 1 * ((m : ℝ) / ((f + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1le he_nonneg
      simpa [mul_one, mul_div_assoc] using hmul
    calc ((growthFunctionVec (halfspaceClass f) j : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ j := hcast
      _ ≤ (2 : ℝ) ^ (f + 1) := le_of_lt (pow_lt_pow_right₀ (by norm_num) hlt)
      _ ≤ (Real.exp 1) ^ (f + 1) := pow_le_pow_left₀ (by norm_num) he2 _
      _ ≤ (Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ)) ^ (f + 1) :=
          pow_le_pow_left₀ he_nonneg he_le _

/-- The type of activations after `i` layers: Euclidean inputs at
layer `0`, Boolean vectors afterwards. -/
@[reducible] def layerTy (d : ℕ) (w : ℕ → ℕ) : ℕ → Type
  | 0 => EuclideanSpace ℝ (Fin d)
  | i + 1 => Fin (w i) → Bool

/-- One neuron reading layer-`i` activations. -/
noncomputable def neuronAt (d : ℕ) (w : ℕ → ℕ) :
    (i : ℕ) → ConceptClass (layerTy d w i) Bool
  | 0 => halfspaceClass d
  | i + 1 => neuronClass (w i)

/-- Fan-in of a layer-`i` neuron. -/
def fanIn (d : ℕ) (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => d
  | i + 1 => w i

/-- A full layer: one neuron per output coordinate. -/
noncomputable def layerAt (d : ℕ) (w : ℕ → ℕ) (i : ℕ) :
    ConceptClass (layerTy d w i) (layerTy d w (i + 1)) :=
  piClass (fun _ => neuronAt d w i)

/-- The trunk of the first `L + 1` layers. -/
noncomputable def trunk (d : ℕ) (w : ℕ → ℕ) :
    (L : ℕ) → ConceptClass (layerTy d w 0) (layerTy d w (L + 1))
  | 0 => layerAt d w 0
  | L + 1 => compClass (trunk d w L) (layerAt d w (L + 1))

/-- The class of sign-activation networks with hidden widths
`w 0, …, w (L - 1)` and one output neuron at layer `L`. -/
noncomputable def networkClass (d : ℕ) (w : ℕ → ℕ) : (L : ℕ) →
    ConceptClass (layerTy d w 0) Bool
  | 0 => neuronAt d w 0
  | L + 1 => compClass (trunk d w L) (neuronAt d w (L + 1))

/-- Per-neuron Sauer bound at layer `i`, capped sizes included. -/
theorem growthFunctionVec_neuronAt_le_real (d : ℕ) (w : ℕ → ℕ) (i j m : ℕ)
    (hjm : j ≤ m) (hf : fanIn d w i + 1 ≤ m) :
    (growthFunctionVec (neuronAt d w i) j : ℝ) ≤
      (Real.exp 1 * (m : ℝ) / (fanIn d w i + 1 : ℕ)) ^ (fanIn d w i + 1) := by
  cases i with
  | zero =>
    simp only [neuronAt, fanIn] at hf ⊢
    exact growthFunctionVec_halfspaceClass_le_real _ _ _ hjm hf
  | succ i =>
    simp only [neuronAt, fanIn] at hf ⊢
    have h1 : growthFunctionVec (neuronClass (w i)) j ≤
        growthFunctionVec (halfspaceClass (w i)) j :=
      growthFunctionVec_neuronClass_le _ _
    have h1r : ((growthFunctionVec (neuronClass (w i)) j : ℕ) : ℝ) ≤
        ((growthFunctionVec (halfspaceClass (w i)) j : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h2 := growthFunctionVec_halfspaceClass_le_real (w i) j m hjm hf
    exact h1r.trans h2

private theorem layerTy_card_succ (d : ℕ) (w : ℕ → ℕ) (i : ℕ) :
    Fintype.card (layerTy d w (i + 1)) = 2 ^ w i := by
  simp only [layerTy]
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Trunk growth is at most the product of the layer growths; each
layer after the first is capped by the cardinality of its Boolean
input type (natural-number assembly). -/
theorem growthFunctionVec_trunk_le (d : ℕ) (w : ℕ → ℕ) (L m : ℕ) :
    growthFunctionVec (trunk d w L) m ≤
      growthFunctionVec (layerAt d w 0) m *
        ∏ i ∈ Finset.range L,
          growthFunctionVec (layerAt d w (i + 1)) (min m (2 ^ w i)) := by
  induction L with
  | zero =>
    simp [trunk]
  | succ L ih =>
    have hcomp := growthFunctionVec_comp_le_card (trunk d w L)
      (layerAt d w (L + 1)) m
    simp only [trunk] at hcomp ⊢
    have hcard := layerTy_card_succ d w L
    rw [hcard] at hcomp
    have hmul := Nat.mul_le_mul_left
      (growthFunctionVec (layerAt d w (L + 1)) (min m (2 ^ w L))) ih
    have hle := hcomp.trans hmul
    rw [Finset.prod_range_succ]
    calc growthFunctionVec (compClass (trunk d w L) (layerAt d w (L + 1))) m
        ≤ growthFunctionVec (layerAt d w (L + 1)) (min m (2 ^ w L)) *
          (growthFunctionVec (layerAt d w 0) m *
            ∏ i ∈ Finset.range L, growthFunctionVec (layerAt d w (i + 1))
              (min m (2 ^ w i))) := hle
      _ = growthFunctionVec (layerAt d w 0) m *
          ((∏ i ∈ Finset.range L, growthFunctionVec (layerAt d w (i + 1))
              (min m (2 ^ w i))) *
            growthFunctionVec (layerAt d w (L + 1)) (min m (2 ^ w L))) := by
          ring

private theorem growthFunctionVec_layerAt_le_pow (d : ℕ) (w : ℕ → ℕ)
    (i j : ℕ) :
    growthFunctionVec (layerAt d w i) j ≤
      (growthFunctionVec (neuronAt d w i) j) ^ w i := by
  unfold layerAt
  have h := growthFunctionVec_pi_le (fun _ : Fin (w i) => neuronAt d w i) j
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

private theorem sauerBase_nonneg (m f : ℕ) :
    (0 : ℝ) ≤ Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ) := by
  apply div_nonneg
  · exact mul_nonneg (le_of_lt (Real.exp_pos 1)) (Nat.cast_nonneg m)
  · exact Nat.cast_nonneg (f + 1)

private theorem sauerFactor_nonneg (m f : ℕ) :
    (0 : ℝ) ≤ (Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ)) ^ (f + 1) :=
  pow_nonneg (sauerBase_nonneg m f) _

private theorem sauerPow_nonneg (m f k : ℕ) :
    (0 : ℝ) ≤
      (((Real.exp 1 * (m : ℝ) / ((f + 1 : ℕ) : ℝ)) ^ (f + 1)) ^ k) :=
  pow_nonneg (sauerFactor_nonneg m f) _

private theorem growthFunctionVec_layerAt_le_real (d : ℕ) (w : ℕ → ℕ)
    (i j m : ℕ) (hjm : j ≤ m) (hf : fanIn d w i + 1 ≤ m) :
    ((growthFunctionVec (layerAt d w i) j : ℕ) : ℝ) ≤
      (((Real.exp 1 * (m : ℝ) / (fanIn d w i + 1 : ℕ)) ^
        (fanIn d w i + 1) : ℝ) ^ w i) := by
  have hpi := growthFunctionVec_layerAt_le_pow d w i j
  have hcast : ((growthFunctionVec (layerAt d w i) j : ℕ) : ℝ) ≤
      (((growthFunctionVec (neuronAt d w i) j : ℕ) : ℝ) ^ w i) := by
    calc ((growthFunctionVec (layerAt d w i) j : ℕ) : ℝ)
        ≤ (((growthFunctionVec (neuronAt d w i) j) ^ w i : ℕ) : ℝ) := by
          exact_mod_cast hpi
      _ = (((growthFunctionVec (neuronAt d w i) j : ℕ) : ℝ) ^ w i) := by
          rw [Nat.cast_pow]
  have hneuron := growthFunctionVec_neuronAt_le_real d w i j m hjm hf
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hneuron (w i)
  exact hcast.trans hpow

private theorem prod_range_succ_first (M : Type) [CommMonoid M]
    (F : ℕ → M) (L : ℕ) :
    ∏ j ∈ Finset.range (L + 1), F j =
      F 0 * ∏ i ∈ Finset.range L, F (i + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_range_succ F (L + 1),
      Finset.prod_range_succ (fun i => F (i + 1)) L, ih,
      mul_assoc]

/-- Network growth is at most the product of the per-neuron Sauer
bounds, one factor per neuron (hidden layers contribute `w i`
factors at fan-in `fanIn d w i`; the output neuron one factor). -/
theorem growthFunctionVec_networkClass_le (d : ℕ) (w : ℕ → ℕ) (L m : ℕ)
    (hm : ∀ i, i ≤ L → fanIn d w i + 1 ≤ m) :
    (growthFunctionVec (networkClass d w L) m : ℝ) ≤
      (∏ i ∈ Finset.range L,
        ((Real.exp 1 * (m : ℝ) / (fanIn d w i + 1 : ℕ)) ^
          (fanIn d w i + 1)) ^ w i) *
      (Real.exp 1 * (m : ℝ) / (fanIn d w L + 1 : ℕ)) ^ (fanIn d w L + 1) := by
  cases L with
  | zero =>
    simp only [networkClass, Finset.range_zero, Finset.prod_empty, one_mul]
    exact growthFunctionVec_neuronAt_le_real d w 0 m m le_rfl (hm 0 le_rfl)
  | succ L =>
    have hcomp := growthFunctionVec_comp_le_card (trunk d w L)
      (neuronAt d w (L + 1)) m
    simp only [networkClass] at hcomp ⊢
    have hcard := layerTy_card_succ d w L
    rw [hcard] at hcomp
    have htrunk := growthFunctionVec_trunk_le d w L m
    have hnat : growthFunctionVec (compClass (trunk d w L)
          (neuronAt d w (L + 1))) m ≤
        growthFunctionVec (neuronAt d w (L + 1)) (min m (2 ^ w L)) *
          (growthFunctionVec (layerAt d w 0) m *
            ∏ i ∈ Finset.range L, growthFunctionVec (layerAt d w (i + 1))
              (min m (2 ^ w i))) :=
      hcomp.trans (Nat.mul_le_mul_left _ htrunk)
    have hcast : ((growthFunctionVec (compClass (trunk d w L)
            (neuronAt d w (L + 1))) m : ℕ) : ℝ) ≤
        ((growthFunctionVec (neuronAt d w (L + 1)) (min m (2 ^ w L)) : ℕ) : ℝ) *
          (((growthFunctionVec (layerAt d w 0) m : ℕ) : ℝ) *
            ∏ i ∈ Finset.range L,
              ((growthFunctionVec (layerAt d w (i + 1))
                (min m (2 ^ w i)) : ℕ) : ℝ)) := by
      calc ((growthFunctionVec (compClass (trunk d w L)
              (neuronAt d w (L + 1))) m : ℕ) : ℝ)
          ≤ (((growthFunctionVec (neuronAt d w (L + 1)) (min m (2 ^ w L)) *
              (growthFunctionVec (layerAt d w 0) m *
                ∏ i ∈ Finset.range L, growthFunctionVec (layerAt d w (i + 1))
                  (min m (2 ^ w i))) : ℕ)) : ℝ) := by exact_mod_cast hnat
        _ = ((growthFunctionVec (neuronAt d w (L + 1)) (min m (2 ^ w L)) : ℕ) :
              ℝ) *
            (((growthFunctionVec (layerAt d w 0) m : ℕ) : ℝ) *
              ∏ i ∈ Finset.range L,
                ((growthFunctionVec (layerAt d w (i + 1))
                  (min m (2 ^ w i)) : ℕ) : ℝ)) := by
            simp [Nat.cast_mul, Nat.cast_prod]
    have hN : ((growthFunctionVec (neuronAt d w (L + 1))
          (min m (2 ^ w L)) : ℕ) : ℝ) ≤
        (Real.exp 1 * (m : ℝ) / (fanIn d w (L + 1) + 1 : ℕ)) ^
          (fanIn d w (L + 1) + 1) :=
      growthFunctionVec_neuronAt_le_real d w (L + 1) (min m (2 ^ w L)) m
        (Nat.min_le_left _ _) (hm (L + 1) le_rfl)
    have hL0 : ((growthFunctionVec (layerAt d w 0) m : ℕ) : ℝ) ≤
        ((((Real.exp 1 * (m : ℝ) / (fanIn d w 0 + 1 : ℕ)) ^
          (fanIn d w 0 + 1) : ℝ)) ^ w 0) :=
      growthFunctionVec_layerAt_le_real d w 0 m m le_rfl
        (hm 0 (Nat.zero_le _))
    have hPi : ∀ i ∈ Finset.range L,
        ((growthFunctionVec (layerAt d w (i + 1)) (min m (2 ^ w i)) : ℕ) : ℝ) ≤
          ((((Real.exp 1 * (m : ℝ) / (fanIn d w (i + 1) + 1 : ℕ)) ^
            (fanIn d w (i + 1) + 1) : ℝ)) ^ w (i + 1)) := by
      intro i hi
      have hiL : i < L := Finset.mem_range.mp hi
      have hiLe : i + 1 ≤ L + 1 := Nat.succ_le_succ hiL.le
      exact growthFunctionVec_layerAt_le_real d w (i + 1) (min m (2 ^ w i))
        m (Nat.min_le_left _ _) (hm (i + 1) hiLe)
    have hprod : ∏ i ∈ Finset.range L,
          ((growthFunctionVec (layerAt d w (i + 1)) (min m (2 ^ w i)) : ℕ) : ℝ) ≤
        ∏ i ∈ Finset.range L,
          ((((Real.exp 1 * (m : ℝ) / (fanIn d w (i + 1) + 1 : ℕ)) ^
            (fanIn d w (i + 1) + 1) : ℝ)) ^ w (i + 1)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Nat.cast_nonneg _
      · exact hPi
    have hL0prod : (((growthFunctionVec (layerAt d w 0) m : ℕ) : ℝ) *
          ∏ i ∈ Finset.range L,
            ((growthFunctionVec (layerAt d w (i + 1))
              (min m (2 ^ w i)) : ℕ) : ℝ)) ≤
        (((((Real.exp 1 * (m : ℝ) / (fanIn d w 0 + 1 : ℕ)) ^
          (fanIn d w 0 + 1) : ℝ)) ^ w 0) *
          ∏ i ∈ Finset.range L,
            ((((Real.exp 1 * (m : ℝ) / (fanIn d w (i + 1) + 1 : ℕ)) ^
              (fanIn d w (i + 1) + 1) : ℝ)) ^ w (i + 1))) :=
      mul_le_mul hL0 hprod
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
        (sauerPow_nonneg m (fanIn d w 0) (w 0))
    have hNS : (0 : ℝ) ≤ (Real.exp 1 * (m : ℝ) /
        (fanIn d w (L + 1) + 1 : ℕ)) ^ (fanIn d w (L + 1) + 1) :=
      sauerFactor_nonneg m (fanIn d w (L + 1))
    have hCnonneg : (0 : ℝ) ≤ (((growthFunctionVec (layerAt d w 0) m : ℕ) : ℝ) *
        ∏ i ∈ Finset.range L,
          ((growthFunctionVec (layerAt d w (i + 1))
            (min m (2 ^ w i)) : ℕ) : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
    have hfinal : ((growthFunctionVec (compClass (trunk d w L)
            (neuronAt d w (L + 1))) m : ℕ) : ℝ) ≤
        (Real.exp 1 * (m : ℝ) / (fanIn d w (L + 1) + 1 : ℕ)) ^
          (fanIn d w (L + 1) + 1) *
          ((((((Real.exp 1 * (m : ℝ) / (fanIn d w 0 + 1 : ℕ)) ^
            (fanIn d w 0 + 1) : ℝ)) ^ w 0) *
            ∏ i ∈ Finset.range L,
              ((((Real.exp 1 * (m : ℝ) / (fanIn d w (i + 1) + 1 : ℕ)) ^
                (fanIn d w (i + 1) + 1) : ℝ)) ^ w (i + 1)))) :=
      hcast.trans (mul_le_mul hN hL0prod hCnonneg hNS)
    have hreindex := prod_range_succ_first ℝ
      (fun i => ((((Real.exp 1 * (m : ℝ) / (fanIn d w i + 1 : ℕ)) ^
        (fanIn d w i + 1) : ℝ)) ^ w i)) L
    rw [hreindex]
    calc ((growthFunctionVec (compClass (trunk d w L)
            (neuronAt d w (L + 1))) m : ℕ) : ℝ)
        ≤ (Real.exp 1 * (m : ℝ) / (fanIn d w (L + 1) + 1 : ℕ)) ^
            (fanIn d w (L + 1) + 1) *
            ((((((Real.exp 1 * (m : ℝ) / (fanIn d w 0 + 1 : ℕ)) ^
              (fanIn d w 0 + 1) : ℝ)) ^ w 0) *
              ∏ i ∈ Finset.range L,
                ((((Real.exp 1 * (m : ℝ) / (fanIn d w (i + 1) + 1 : ℕ)) ^
                  (fanIn d w (i + 1) + 1) : ℝ)) ^ w (i + 1)))) := hfinal
      _ = (((((Real.exp 1 * (m : ℝ) / (fanIn d w 0 + 1 : ℕ)) ^
          (fanIn d w 0 + 1) : ℝ)) ^ w 0) *
          ∏ i ∈ Finset.range L,
            ((((Real.exp 1 * (m : ℝ) / (fanIn d w (i + 1) + 1 : ℕ)) ^
              (fanIn d w (i + 1) + 1) : ℝ)) ^ w (i + 1))) *
          (Real.exp 1 * (m : ℝ) / (fanIn d w (L + 1) + 1 : ℕ)) ^
            (fanIn d w (L + 1) + 1) := by ring

/-- Number of neurons at layer `i` of an `L`-hidden-layer network. -/
def widthAt (w : ℕ → ℕ) (L i : ℕ) : ℕ := if i < L then w i else 1

/-- Total weights and biases of the architecture. -/
def paramCount (d : ℕ) (w : ℕ → ℕ) (L : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (L + 1), (fanIn d w i + 1) * widthAt w L i

/-- Collapsed form: network growth is at most `(e * m) ^ E`. -/
theorem growthFunctionVec_networkClass_le_exp_pow (d : ℕ) (w : ℕ → ℕ)
    (L m : ℕ) (hm : ∀ i, i ≤ L → fanIn d w i + 1 ≤ m) :
    (growthFunctionVec (networkClass d w L) m : ℝ) ≤
      (Real.exp 1 * (m : ℝ)) ^ paramCount d w L := by
  have hnet := growthFunctionVec_networkClass_le d w L m hm
  have hem_nonneg : (0 : ℝ) ≤ Real.exp 1 * (m : ℝ) :=
    mul_nonneg (le_of_lt (Real.exp_pos 1)) (Nat.cast_nonneg m)
  have hbase_le : ∀ i, Real.exp 1 * (m : ℝ) / ((fanIn d w i + 1 : ℕ) : ℝ) ≤
      Real.exp 1 * (m : ℝ) := by
    intro i
    apply div_le_self hem_nonneg
    have h1 : (1 : ℕ) ≤ fanIn d w i + 1 := by omega
    exact_mod_cast h1
  have hS_le : ∀ i, (Real.exp 1 * (m : ℝ) / ((fanIn d w i + 1 : ℕ) : ℝ)) ^
      (fanIn d w i + 1) ≤ (Real.exp 1 * (m : ℝ)) ^ (fanIn d w i + 1) := by
    intro i
    exact pow_le_pow_left₀ (sauerBase_nonneg m (fanIn d w i)) (hbase_le i) _
  have hSpow_le : ∀ i, (((Real.exp 1 * (m : ℝ) /
      ((fanIn d w i + 1 : ℕ) : ℝ)) ^ (fanIn d w i + 1) : ℝ) ^ w i) ≤
      (Real.exp 1 * (m : ℝ)) ^ ((fanIn d w i + 1) * w i) := by
    intro i
    calc ((((Real.exp 1 * (m : ℝ) / ((fanIn d w i + 1 : ℕ) : ℝ)) ^
          (fanIn d w i + 1) : ℝ)) ^ w i)
        ≤ ((((Real.exp 1 * (m : ℝ)) ^ (fanIn d w i + 1) : ℝ)) ^ w i) :=
          pow_le_pow_left₀ (sauerFactor_nonneg m (fanIn d w i)) (hS_le i) _
      _ = (Real.exp 1 * (m : ℝ)) ^ ((fanIn d w i + 1) * w i) := by
          rw [← pow_mul]
  have hprod : ∏ i ∈ Finset.range L,
        ((((Real.exp 1 * (m : ℝ) / ((fanIn d w i + 1 : ℕ) : ℝ)) ^
          (fanIn d w i + 1) : ℝ)) ^ w i) ≤
      ∏ i ∈ Finset.range L,
        (Real.exp 1 * (m : ℝ)) ^ ((fanIn d w i + 1) * w i) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact sauerPow_nonneg m (fanIn d w i) (w i)
    · intro i _
      exact hSpow_le i
  have hL := hS_le L
  have hmul : (∏ i ∈ Finset.range L,
          ((((Real.exp 1 * (m : ℝ) / ((fanIn d w i + 1 : ℕ) : ℝ)) ^
            (fanIn d w i + 1) : ℝ)) ^ w i)) *
        (Real.exp 1 * (m : ℝ) / ((fanIn d w L + 1 : ℕ) : ℝ)) ^
          (fanIn d w L + 1) ≤
      (∏ i ∈ Finset.range L,
        (Real.exp 1 * (m : ℝ)) ^ ((fanIn d w i + 1) * w i)) *
        (Real.exp 1 * (m : ℝ)) ^ (fanIn d w L + 1) :=
    mul_le_mul hprod hL (sauerFactor_nonneg m (fanIn d w L))
      (Finset.prod_nonneg (fun i _ => pow_nonneg hem_nonneg _))
  have hprod_eq : ∏ i ∈ Finset.range L,
        (Real.exp 1 * (m : ℝ)) ^ ((fanIn d w i + 1) * w i) =
      (Real.exp 1 * (m : ℝ)) ^
        (∑ i ∈ Finset.range L, (fanIn d w i + 1) * w i) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  have hpc : paramCount d w L =
      (∑ i ∈ Finset.range L, (fanIn d w i + 1) * w i) +
        (fanIn d w L + 1) := by
    unfold paramCount
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hiL : i < L := Finset.mem_range.mp hi
      simp [widthAt, hiL]
    · simp [widthAt]
  calc ((growthFunctionVec (networkClass d w L) m : ℕ) : ℝ)
      ≤ (∏ i ∈ Finset.range L,
          ((((Real.exp 1 * (m : ℝ) / ((fanIn d w i + 1 : ℕ) : ℝ)) ^
            (fanIn d w i + 1) : ℝ)) ^ w i)) *
          (Real.exp 1 * (m : ℝ) / ((fanIn d w L + 1 : ℕ) : ℝ)) ^
            (fanIn d w L + 1) := hnet
    _ ≤ (∏ i ∈ Finset.range L,
          (Real.exp 1 * (m : ℝ)) ^ ((fanIn d w i + 1) * w i)) *
          (Real.exp 1 * (m : ℝ)) ^ (fanIn d w L + 1) := hmul
    _ = (Real.exp 1 * (m : ℝ)) ^
          (∑ i ∈ Finset.range L, (fanIn d w i + 1) * w i) *
          (Real.exp 1 * (m : ℝ)) ^ (fanIn d w L + 1) := by rw [hprod_eq]
    _ = (Real.exp 1 * (m : ℝ)) ^
          ((∑ i ∈ Finset.range L, (fanIn d w i + 1) * w i) +
            (fanIn d w L + 1)) := by rw [← pow_add]
    _ = (Real.exp 1 * (m : ℝ)) ^ paramCount d w L := by rw [← hpc]

end Cslib.MachineLearning.PACLearning
