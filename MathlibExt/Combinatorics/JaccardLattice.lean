/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Jaccard distance triangle inequality on arbitrary lattices

Generalized Jaccard distance from a real-valued lattice valuation, following
`https://arxiv.org/abs/2608.18194v1` (Badica–Badica).

Scope: arbitrary lattices with no distributivity, complements, bounds,
finiteness, or strict monotonicity. Proves the Gilbert condition is equivalent
to modularity plus monotonicity, and the triangle inequality from the Gilbert
condition (hence for strictly positive monotone modular valuations). This is a
triangle inequality only, not a `PseudoMetricSpace` instance.
-/

@[expose] public section

namespace JaccardLattice

variable {L : Type*} [Lattice L]

/-- **Modular valuation.** A function $f \colon L \to \mathbb{R}$ on a lattice $L$, with join
$\vee$ and meet $\wedge$, is a modular valuation when
$f(X) + f(Y) = f(X \vee Y) + f(X \wedge Y)$ for all $X, Y \in L$. -/
def IsModularValuation (f : L → ℝ) : Prop :=
  ∀ X Y, f X + f Y = f (X ⊔ Y) + f (X ⊓ Y)

/-- **Strictly positive valuation.** A function $f \colon L \to \mathbb{R}$ on a lattice
$L$ is strictly positive when $f(X) > 0$ for every $X \in L$. -/
def IsStrictlyPositive (f : L → ℝ) : Prop :=
  ∀ X, 0 < f X

/-- **Gilbert condition.** A function $f \colon L \to \mathbb{R}$ on a lattice $L$, with join
$\vee$ and meet $\wedge$, satisfies the Gilbert condition when
$f(X \vee Z) + f(Z \vee Y) + f(X \wedge Y) \ge
f(X \wedge Z) + f(Z \wedge Y) + f(X \vee Y \vee Z)$ for all $X, Y, Z \in L$. -/
def GilbertCondition (f : L → ℝ) : Prop :=
  ∀ X Y Z, f (X ⊔ Z) + f (Z ⊔ Y) + f (X ⊓ Y) ≥
    f (X ⊓ Z) + f (Z ⊓ Y) + f (X ⊔ Y ⊔ Z)

/-- **Generalized Jaccard distance.** For a function $f \colon L \to \mathbb{R}$ on a lattice
$L$ with join $\vee$ and meet $\wedge$, the Jaccard distance of $X, Y \in L$ is
$d_f(X, Y) = 1 - f(X \wedge Y) / f(X \vee Y)$.

Division by zero is taken to give $0$, so $d_f(X, Y) = 1$ when $f(X \vee Y) = 0$. -/
noncomputable def jaccardDist (f : L → ℝ) (X Y : L) : ℝ :=
  1 - f (X ⊓ Y) / f (X ⊔ Y)

private theorem modularAndMonotone_of_gilbertCondition {f : L → ℝ}
    (hG : GilbertCondition f) : IsModularValuation f ∧ Monotone f := by
  have low : ∀ P Q : L, f P + f Q ≥ f (P ⊔ Q) + f (P ⊓ Q) := by
    intro P Q
    have hg := hG P Q (P ⊓ Q)
    have s1 : P ⊔ (P ⊓ Q) = P :=
      le_antisymm (sup_le le_rfl inf_le_left) le_sup_left
    have s2 : (P ⊓ Q) ⊔ Q = Q :=
      le_antisymm (sup_le inf_le_right le_rfl) le_sup_right
    have s3 : P ⊓ (P ⊓ Q) = P ⊓ Q :=
      le_antisymm inf_le_right (le_inf inf_le_left le_rfl)
    have s4 : (P ⊓ Q) ⊓ Q = P ⊓ Q :=
      le_antisymm inf_le_left (le_inf le_rfl inf_le_right)
    have s5 : P ⊔ Q ⊔ (P ⊓ Q) = P ⊔ Q :=
      le_antisymm (sup_le le_rfl (le_trans inf_le_left le_sup_left)) le_sup_left
    rw [s1, s2, s3, s4, s5] at hg
    linarith
  have high : ∀ P Q : L, f (P ⊔ Q) + f (P ⊓ Q) ≥ f P + f Q := by
    intro P Q
    have hg := hG P Q (P ⊔ Q)
    have t1 : P ⊔ (P ⊔ Q) = P ⊔ Q :=
      le_antisymm (sup_le le_sup_left le_rfl) le_sup_right
    have t2 : (P ⊔ Q) ⊔ Q = P ⊔ Q :=
      le_antisymm (sup_le le_rfl le_sup_right) le_sup_left
    have t3 : P ⊓ (P ⊔ Q) = P :=
      le_antisymm inf_le_left (le_inf le_rfl le_sup_left)
    have t4 : (P ⊔ Q) ⊓ Q = Q :=
      le_antisymm inf_le_right (le_inf le_sup_right le_rfl)
    have t5 : P ⊔ Q ⊔ (P ⊔ Q) = P ⊔ Q :=
      le_antisymm (sup_le le_rfl le_rfl) le_sup_left
    rw [t1, t2, t3, t4, t5] at hg
    linarith
  have hmod : IsModularValuation f := by
    intro P Q
    have a1 := low P Q
    have a2 := high P Q
    linarith
  have hmono : Monotone f := by
    intro P Q hPQ
    have hg := hG Q Q P
    have w1 : Q ⊔ P = Q := le_antisymm (sup_le le_rfl hPQ) le_sup_left
    have w2 : P ⊔ Q = Q := le_antisymm (sup_le hPQ le_rfl) le_sup_right
    have w3 : Q ⊓ Q = Q := le_antisymm inf_le_left (le_inf le_rfl le_rfl)
    have w4 : Q ⊓ P = P := le_antisymm inf_le_right (le_inf hPQ le_rfl)
    have w5 : P ⊓ Q = P := le_antisymm inf_le_left (le_inf le_rfl hPQ)
    have w6 : Q ⊔ Q ⊔ P = Q :=
      le_antisymm (sup_le (sup_le le_rfl le_rfl) hPQ)
        (le_trans le_sup_left le_sup_left)
    rw [w1, w2, w3, w4, w5, w6] at hg
    linarith
  exact ⟨hmod, hmono⟩

private theorem gilbertCondition_of_modularAndMonotone {f : L → ℝ}
    (hM : IsModularValuation f) (hmono : Monotone f) : GilbertCondition f := by
  intro X Y Z
  have r1 : f (X ⊔ Z) + f Y = f (X ⊔ Y ⊔ Z) + f ((X ⊔ Z) ⊓ Y) := by
    have h := hM (X ⊔ Z) Y
    have hj : (X ⊔ Z) ⊔ Y = X ⊔ Y ⊔ Z := by
      rw [sup_assoc, sup_comm Z Y, ← sup_assoc]
    rw [hj] at h
    linarith
  have r2 : f (X ⊓ Z) + f Y = f ((X ⊓ Z) ⊔ Y) + f (X ⊓ Y ⊓ Z) := by
    have h := hM (X ⊓ Z) Y
    have hm : (X ⊓ Z) ⊓ Y = X ⊓ Y ⊓ Z := by
      rw [inf_assoc, inf_comm Z Y, ← inf_assoc]
    rw [hm] at h
    linarith
  have n1 : f ((X ⊓ Z) ⊔ Y) ≤ f (Z ⊔ Y) :=
    hmono (sup_le_sup inf_le_right le_rfl)
  have n2 : f (Z ⊓ Y) ≤ f ((X ⊔ Z) ⊓ Y) :=
    hmono (inf_le_inf le_sup_right le_rfl)
  have n3 : f (X ⊓ Y ⊓ Z) ≤ f (X ⊓ Y) := hmono inf_le_left
  linarith

/-- **Characterization of the Gilbert condition.** A function $f \colon L \to \mathbb{R}$
on a lattice $L$ satisfies the Gilbert condition if and only if $f$ is a modular valuation
and is monotone, that is, $X \le Y$ implies $f(X) \le f(Y)$. -/
theorem gilbertCondition_iff {f : L → ℝ} :
    GilbertCondition f ↔ IsModularValuation f ∧ Monotone f :=
  ⟨modularAndMonotone_of_gilbertCondition,
    fun h => gilbertCondition_of_modularAndMonotone h.1 h.2⟩

/-- **Jaccard distance as a single quotient.** Let $f \colon L \to \mathbb{R}$ be a strictly
positive function on a lattice $L$, with join $\vee$ and meet $\wedge$. Then for all
$X, Y \in L$ the Jaccard distance of $X$ and $Y$ with respect to $f$ is
$d_f(X, Y) = (f(X \vee Y) - f(X \wedge Y)) / f(X \vee Y)$. -/
theorem jaccardDist_eq_div {f : L → ℝ} (hpos : IsStrictlyPositive f) (X Y : L) :
    jaccardDist f X Y = (f (X ⊔ Y) - f (X ⊓ Y)) / f (X ⊔ Y) := by
  unfold jaccardDist
  have hne : f (X ⊔ Y) ≠ 0 := ne_of_gt (hpos _)
  rw [← div_self hne, ← sub_div]

/-- **Jaccard triangle inequality under the Gilbert condition.** Let
$f \colon L \to \mathbb{R}$ be a strictly positive function on a lattice $L$ that satisfies
the Gilbert condition, and let $d_f$ be the Jaccard distance of $f$. Then
$d_f(U, W) + d_f(W, V) \ge d_f(U, V)$ for all $U, V, W \in L$. -/
theorem jaccardDist_triangle_of_gilbertCondition {f : L → ℝ}
    (hG : GilbertCondition f) (hpos : IsStrictlyPositive f) (U V W : L) :
    jaccardDist f U W + jaccardDist f W V ≥ jaccardDist f U V := by
  have hmono : Monotone f := (modularAndMonotone_of_gilbertCondition hG).2
  have hT : 0 < f (U ⊔ V ⊔ W) := hpos _
  have hUV : 0 < f (U ⊔ V) := hpos _
  have hUW : 0 < f (U ⊔ W) := hpos _
  have hWV : 0 < f (W ⊔ V) := hpos _
  have cUV : f (U ⊔ V) ≤ f (U ⊔ V ⊔ W) := hmono le_sup_left
  have cUW : f (U ⊔ W) ≤ f (U ⊔ V ⊔ W) :=
    hmono (sup_le (le_trans le_sup_left le_sup_left) le_sup_right)
  have cWV : f (W ⊔ V) ≤ f (U ⊔ V ⊔ W) :=
    hmono (sup_le le_sup_right (le_trans le_sup_right le_sup_left))
  have zUW : 0 ≤ f (U ⊔ W) - f (U ⊓ W) :=
    sub_nonneg.mpr (hmono (le_trans inf_le_left le_sup_left))
  have zWV : 0 ≤ f (W ⊔ V) - f (W ⊓ V) :=
    sub_nonneg.mpr (hmono (le_trans inf_le_left le_sup_left))
  have zUV : 0 ≤ f (U ⊓ V) := le_of_lt (hpos _)
  have loUW : (f (U ⊔ W) - f (U ⊓ W)) / f (U ⊔ V ⊔ W) ≤ jaccardDist f U W := by
    rw [jaccardDist_eq_div hpos U W, div_le_div_iff₀ hT hUW]
    exact mul_le_mul_of_nonneg_left cUW zUW
  have loWV : (f (W ⊔ V) - f (W ⊓ V)) / f (U ⊔ V ⊔ W) ≤ jaccardDist f W V := by
    rw [jaccardDist_eq_div hpos W V, div_le_div_iff₀ hT hWV]
    exact mul_le_mul_of_nonneg_left cWV zWV
  have upUV : jaccardDist f U V ≤
      (f (U ⊔ V ⊔ W) - f (U ⊓ V)) / f (U ⊔ V ⊔ W) := by
    have hd : f (U ⊓ V) / f (U ⊔ V ⊔ W) ≤ f (U ⊓ V) / f (U ⊔ V) := by
      rw [div_le_div_iff₀ hT hUV]
      exact mul_le_mul_of_nonneg_left cUV zUV
    have he : (f (U ⊔ V ⊔ W) - f (U ⊓ V)) / f (U ⊔ V ⊔ W)
        = 1 - f (U ⊓ V) / f (U ⊔ V ⊔ W) := by
      rw [sub_div, div_self (ne_of_gt hT)]
    unfold jaccardDist
    rw [he]
    linarith
  have hg3 := hG U V W
  have hsum : (f (U ⊔ V ⊔ W) - f (U ⊓ V)) / f (U ⊔ V ⊔ W)
      ≤ (f (U ⊔ W) - f (U ⊓ W)) / f (U ⊔ V ⊔ W)
        + (f (W ⊔ V) - f (W ⊓ V)) / f (U ⊔ V ⊔ W) := by
    rw [← add_div, div_le_div_iff_of_pos_right hT]
    linarith
  linarith

/-- **Triangle inequality for the generalized Jaccard distance.** Let
$f \colon L \to \mathbb{R}$ be a strictly positive, monotone modular valuation on a lattice
$L$, and let $d_f$ be the Jaccard distance of $f$. Then
$d_f(U, W) + d_f(W, V) \ge d_f(U, V)$ for all $U, V, W \in L$. -/
theorem jaccardDist_triangle {f : L → ℝ} (hM : IsModularValuation f)
    (hmono : Monotone f) (hpos : IsStrictlyPositive f) (U V W : L) :
    jaccardDist f U W + jaccardDist f W V ≥ jaccardDist f U V :=
  jaccardDist_triangle_of_gilbertCondition
    (gilbertCondition_of_modularAndMonotone hM hmono) hpos U V W

end JaccardLattice
