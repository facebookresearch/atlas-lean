/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PathSignature.ExtensionTheorem

open MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.ExtensionTheorem

-- With `p = 1`, the increments of a path with continuous velocity determine every multiplicative
-- functional of finite `1`-variation extending them: it is the signature of the path, in every
-- degree it has.
example {v : Fin 2 → ℝ → ℝ} (hv : ∀ i, Continuous (v i)) (m : ℕ)
    (Z : ℝ → ℝ → List (Fin 2) → ℝ)
    (hZ1 : ∀ s t, s ≤ t → ∀ w : List (Fin 2), w.length ≤ 1 → Z s t w = signature v s t w)
    (hZ : IsMultiplicativeFunctional m Z Set.univ) (hZp : HasFinitePVariation 1 m Z Set.univ)
    {s t : ℝ} (hst : s ≤ t) (w : List (Fin 2)) (hw : w.length ≤ m) :
    Z s t w = signature v s t w := by
  have hint : ∀ i a b, IntervalIntegrable (v i) MeasureTheory.volume a b := fun i a b =>
    (hv i).intervalIntegrable a b
  obtain ⟨Y, -, -, huniq⟩ := ExtensionTheoremWanted.exists_unique_extension le_rfl
    Set.ordConnected_univ (signature v) (isMultiplicativeFunctional_signature hint _ _)
    (hasFinitePVariation_signature hv _ _)
  rw [huniq m Z (fun a _ b _ hab u hu => hZ1 a b hab u (by simpa using hu)) hZ hZp s trivial t
      trivial hst w hw,
    huniq m (signature v) (fun _ _ _ _ _ _ _ => rfl) (isMultiplicativeFunctional_signature hint _ _)
      (hasFinitePVariation_signature hv _ _) s trivial t trivial hst w hw]

-- A multiplicative functional of every degree with finite `p`-variation is determined by its
-- first `⌊p⌋` levels.
example {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p) {J : Set ℝ} (hJ : J.OrdConnected)
    (Y Z : ℝ → ℝ → List ι → ℝ)
    (hY : ∀ m, IsMultiplicativeFunctional m Y J ∧ HasFinitePVariation p m Y J)
    (hZ : ∀ m, IsMultiplicativeFunctional m Z J ∧ HasFinitePVariation p m Z J)
    (hYZ : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Z s t w = Y s t w) :
    ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, Z s t w = Y s t w := by
  obtain ⟨E, -, -, huniq⟩ :=
    ExtensionTheoremWanted.exists_unique_extension hp hJ Y (hY _).1 (hY _).2
  intro s hs t ht hst w
  rw [huniq w.length Z hYZ (hZ _).1 (hZ _).2 s hs t ht hst w le_rfl,
    huniq w.length Y (fun _ _ _ _ _ _ _ => rfl) (hY _).1 (hY _).2 s hs t ht hst w le_rfl]

-- The constant path in `ℝ²` has no positive levels, so the zero control gives it finite
-- `p`-variation in every degree.
private theorem levelNorm_signature_const (s t : ℝ) (hst : s ≤ t) {i : ℕ} (hi : 1 ≤ i) :
    levelNorm (signature (fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) s t) i = 0 := by
  rw [signature_of_eqOn_Ioc (v := fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) 0 hst fun _ _ _ => rfl]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hi
  simp [levelNorm, tensorExp, List.ofFn_succ]

private theorem hasFinitePVariation_signature_const {p : ℝ} (hp : 0 < p) (m : ℕ) (J : Set ℝ) :
    HasFinitePVariation p m (signature fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) J :=
  ⟨fun _ _ => 0, ⟨continuousOn_const, fun _ _ => rfl, fun _ _ _ _ _ => le_rfl, by simp⟩, 1,
    one_pos, fun i hi _ s _ t _ hst => by
      rw [levelNorm_signature_const s t hst hi, Real.zero_rpow (by positivity), zero_div]⟩

-- A genuinely rough exponent, `p = 5 / 2`, with the two levels `⌊5 / 2⌋ = 2` of the constant
-- path prescribed: the extension exists, and it has no positive levels.
example : ∃ Y : ℝ → ℝ → List (Fin 2) → ℝ,
    (∀ m, IsMultiplicativeFunctional m Y Set.univ ∧ HasFinitePVariation (5 / 2) m Y Set.univ) ∧
      ∀ s t, s ≤ t → ∀ w : List (Fin 2), w ≠ [] → Y s t w = 0 := by
  have hmult (m : ℕ) : IsMultiplicativeFunctional m
      (signature fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) Set.univ :=
    isMultiplicativeFunctional_signature (fun _ _ _ => intervalIntegrable_const) _ _
  obtain ⟨Y, -, hY, huniq⟩ := ExtensionTheoremWanted.exists_unique_extension (p := 5 / 2)
    (by norm_num) Set.ordConnected_univ _ (hmult _)
    (hasFinitePVariation_signature_const (by norm_num) _ _)
  refine ⟨Y, hY, fun s t hst w hw => ?_⟩
  rw [← huniq w.length _ (fun _ _ _ _ _ _ _ => rfl) (hmult _)
      (hasFinitePVariation_signature_const (by norm_num) _ _) s trivial t trivial hst w le_rfl,
    signature_of_eqOn_Ioc (v := fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) 0 hst fun _ _ _ => rfl]
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [tensorExp]

end MathlibExtTest.Analysis.PathSignature.ExtensionTheorem
