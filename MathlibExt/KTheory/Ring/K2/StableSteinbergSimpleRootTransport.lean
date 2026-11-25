/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleRootComplement
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylPermutationTrivial

/-! # Finite-Weyl permutation and positive simple-root transport

Reusable prerequisite for the Lemma-25 double-coset packet, per read-only
scout `90306`.

* A noncomputable `MonoidHom` `finiteWeylPerm n` from the subtype
  `↥(finiteWeylSubgroup (R := F) n)` to `Equiv.Perm (Fin n)`. On a bounded
  Weyl word `(m, a, b, u)` its value is the head-left product of the
  corresponding `Equiv.swap`s. Representation independence is proved by
  forming the forward word concatenated with the reversed, negated-unit
  inverse word and applying the already-accepted
  `finiteWeyl_word_perm_prod_eq_one` to its `toStableE` image.
* A reusable bounded-word conjugation theorem `finiteWeyl_conj_x`: conjugating
  `x p q c` by a finite-Weyl element yields one root element whose indices are
  the induced permutation images. The single-generator step uses the six
  existing `weyl_conj_x_*` identities plus the disjoint-commutation pattern,
  with an exhaustive equality/shared/disjoint split. Coefficients remain
  existential; the index orientation is exact.
* The positive simple-root transport theorem
  `finiteWeyl_simpleRoot_mem_borel`: for `hm : m + 1 < n`, positivity of the
  induced permutation on `m, m + 1`, and `g ∈ simpleRootSubgroup m`, the
   conjugate `w * g * w⁻¹` lies in `finiteBorelSubgroup n`.
* The representation-choice specification `finiteWeylPerm_exists_repr` is
  public because the homomorphism's choice data cannot rest on a private
  lemma under `@[expose]`; representation independence itself stays in the
  private `swapProd_eq_of_weylProd_eq`.

Orientation: conjugation is always `w * y * w⁻¹` (conjugator on the left).
`List.prod [σ₀, σ₁] = σ₀ * σ₁` is head-left: `List.ofFn` lists
`f 0, f 1, …` and `List.prod (x :: xs) = x * xs.prod`. For permutations,
`Equiv.Perm.mul_apply : (σ * τ) i = σ (τ i)`, so in a head-left product the
tail acts first and the head acts outermost last. The Weyl word and the swap
word use the same head-left order, so word concatenation corresponds to group
multiplication on both sides (`List.prod_append`, `List.ofFn_fin_append`).

Hypotheses are always explicit: bounded-word indices satisfy `a k < n`,
`b k < n`, `a k ≠ b k`; single conjugation needs `p < n`, `q < n`,
`p ≠ q`; transport needs `hm : m + 1 < n` plus permutation positivity
`(perm w ⟨m, _⟩).val < (perm w ⟨m + 1, _⟩).val`.

Nonclaims: no Steinberg-word Bruhat existence/uniqueness, Matsumoto theorem,
`ker toStableE ≤ torusCocycleSubgroup`, quotient injectivity, rejected
lower-remainder recursion, or later Lemma-25/double-coset theorem is used.
Matrix Bruhat middle uniqueness is used only through the already-accepted
`finiteWeyl_word_perm_prod_eq_one`; it is not rebuilt. No torus-transport,
quotient, Matsumoto, or Bruhat module is imported.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

open Matrix.GeneralLinearGroup

/-- Reverse `ofFn` through `Fin.rev`; no pinned lemma supplies this. -/
private theorem ofFn_comp_fin_rev {α : Type*} {m : ℕ} (f : Fin m → α) :
    (List.ofFn f).reverse = List.ofFn fun k => f (Fin.rev k) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
    congr 1
    apply Fin.ext
    change m - 1 - i = m - (i + 1)
    omega

-- The `set` unfolding equations below are unreferenced after the minimal
-- `rfl`/`funext` closers; the bound witnesses stay in the terms themselves.
set_option linter.unusedVariables false in
/-- Representation independence for the swap product: two bounded Weyl words
with the same head-left `weyl` product have the same head-left `swap`
product. The proof concatenates the forward word with the reversed,
negated-unit inverse of the second word; that ratio word has `weyl` product
`1`, hence `toStableE` image `1`, so the accepted
`finiteWeyl_word_perm_prod_eq_one` forces its `swap` product to `1`, and
self-inverse reversed swaps give equality of the two swap products. -/
private theorem swapProd_eq_of_weylProd_eq {n m₁ m₂ : ℕ}
    {a₁ b₁ : Fin m₁ → ℕ} {ha₁ : ∀ k, a₁ k < n} {hb₁ : ∀ k, b₁ k < n}
    {hab₁ : ∀ k, a₁ k ≠ b₁ k} {u₁ : Fin m₁ → Fˣ}
    {a₂ b₂ : Fin m₂ → ℕ} {ha₂ : ∀ k, a₂ k < n} {hb₂ : ∀ k, b₂ k < n}
    {hab₂ : ∀ k, a₂ k ≠ b₂ k} {u₂ : Fin m₂ → Fˣ}
    (h_eq : (List.ofFn fun k =>
      weyl (R := F) (a₁ k) (b₁ k) (hab₁ k) (u₁ k)).prod =
      (List.ofFn fun k =>
        weyl (R := F) (a₂ k) (b₂ k) (hab₂ k) (u₂ k)).prod) :
    (List.ofFn fun k =>
      Equiv.swap (⟨a₁ k, ha₁ k⟩ : Fin n) (⟨b₁ k, hb₁ k⟩ : Fin n)).prod =
    (List.ofFn fun k =>
      Equiv.swap (⟨a₂ k, ha₂ k⟩ : Fin n) (⟨b₂ k, hb₂ k⟩ : Fin n)).prod := by
  classical
  let word₁ := FiniteWeylWord.ofBoundedNat a₁ b₁ ha₁ hb₁ hab₁ u₁
  let word₂ := FiniteWeylWord.ofBoundedNat a₂ b₂ ha₂ hb₂ hab₂ u₂
  have h_eq_word : evalFiniteWeylWord word₁ = evalFiniteWeylWord word₂ := by
    rw [evalFiniteWeylWord_ofBoundedNat,
      evalFiniteWeylWord_ofBoundedNat]
    exact h_eq
  set a₂r : Fin m₂ → ℕ := fun k => a₂ (Fin.rev k) with ha₂r_def
  set b₂r : Fin m₂ → ℕ := fun k => b₂ (Fin.rev k) with hb₂r_def
  set u₂r : Fin m₂ → Fˣ := fun k => -(u₂ (Fin.rev k)) with hu₂r_def
  have ha₂r : ∀ k, a₂r k < n := fun k => ha₂ _
  have hb₂r : ∀ k, b₂r k < n := fun k => hb₂ _
  have hab₂r : ∀ k, a₂r k ≠ b₂r k := fun k => hab₂ _
  have ha : ∀ k : Fin (m₁ + m₂), (Fin.append a₁ a₂r) k < n := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      exact ha₁ i
    · rw [Fin.append_right]
      exact ha₂r i
  have hb : ∀ k : Fin (m₁ + m₂), (Fin.append b₁ b₂r) k < n := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      exact hb₁ i
    · rw [Fin.append_right]
      exact hb₂r i
  have hab : ∀ k : Fin (m₁ + m₂),
      (Fin.append a₁ a₂r) k ≠ (Fin.append b₁ b₂r) k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left, Fin.append_left]
      exact hab₁ i
    · rw [Fin.append_right, Fin.append_right]
      exact hab₂r i
  set hu : Fin (m₁ + m₂) → Fˣ := Fin.append u₁ u₂r with hu_def
  let word₂r := FiniteWeylWord.ofBoundedNat a₂r b₂r ha₂r hb₂r hab₂r u₂r
  let ratioWord := FiniteWeylWord.ofBoundedNat
    (Fin.append a₁ a₂r) (Fin.append b₁ b₂r) ha hb hab hu
  have hWeylInv : evalFiniteWeylWord word₂r =
      (evalFiniteWeylWord word₂)⁻¹ := by
    rw [evalFiniteWeylWord_ofBoundedNat,
      evalFiniteWeylWord_ofBoundedNat]
    have h1 : ((List.ofFn fun k : Fin m₂ =>
        weyl (R := F) (a₂ k) (b₂ k) (hab₂ k) (u₂ k)).map fun x => x⁻¹).reverse =
        List.ofFn fun k : Fin m₂ =>
          weyl (R := F) (a₂r k) (b₂r k) (hab₂r k) (u₂r k) := by
      rw [List.map_ofFn, ofFn_comp_fin_rev]
      congr 1
      exact funext fun k => (weyl_neg_eq_inv (R := F) _ _ _ _).symm
    have h2 := List.prod_inv_reverse (List.ofFn fun k : Fin m₂ =>
      weyl (R := F) (a₂ k) (b₂ k) (hab₂ k) (u₂ k))
    rw [h1] at h2
    exact h2.symm
  have hSwapInv : FiniteWeylWord.permEval word₂r =
      (FiniteWeylWord.permEval word₂)⁻¹ := by
    rw [FiniteWeylWord.permEval_ofBoundedNat,
      FiniteWeylWord.permEval_ofBoundedNat]
    have h1 : ((List.ofFn fun k : Fin m₂ =>
        Equiv.swap (⟨a₂ k, ha₂ k⟩ : Fin n) (⟨b₂ k, hb₂ k⟩ : Fin n)).map
        fun x => x⁻¹).reverse =
        List.ofFn fun k : Fin m₂ =>
          Equiv.swap (⟨a₂r k, ha₂r k⟩ : Fin n) (⟨b₂r k, hb₂r k⟩ : Fin n) := by
      rw [List.map_ofFn, ofFn_comp_fin_rev]
      rfl
    have h2 := List.prod_inv_reverse (List.ofFn fun k : Fin m₂ =>
      Equiv.swap (⟨a₂ k, ha₂ k⟩ : Fin n) (⟨b₂ k, hb₂ k⟩ : Fin n))
    rw [h1] at h2
    exact h2.symm
  have hwordAppend : ratioWord = word₁ ++ word₂r := by
    unfold ratioWord word₁ word₂r FiniteWeylWord.ofBoundedNat
    rw [← List.ofFn_fin_append]
    congr 1
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
      simp [Fin.append_left, Fin.append_right, hu_def]
  have hWtot : evalFiniteWeylWord ratioWord = 1 := by
    rw [hwordAppend, evalFiniteWeylWord_append, hWeylInv,
      h_eq_word, mul_inv_cancel]
  have hWImage : toStableE (R := F) (evalFiniteWeylWord ratioWord) = 1 := by
    rw [hWtot, map_one]
  have hWImageRaw : toStableE (R := F)
      ((List.ofFn fun k : Fin (m₁ + m₂) => weyl (R := F)
        ((Fin.append a₁ a₂r) k) ((Fin.append b₁ b₂r) k)
          (hab k) (hu k)).prod) = 1 := by
    rw [← evalFiniteWeylWord_ofBoundedNat]
    exact hWImage
  have hStotRaw := Matrix.GeneralLinearGroup.finiteWeyl_word_perm_prod_eq_one
    (F := F) (Fin.append a₁ a₂r) (Fin.append b₁ b₂r)
      ha hb hab hu hWImageRaw
  have hStot : FiniteWeylWord.permEval ratioWord = 1 := by
    rw [FiniteWeylWord.permEval_ofBoundedNat]
    exact hStotRaw
  have hpermEq : FiniteWeylWord.permEval word₁ =
      FiniteWeylWord.permEval word₂ := by
    rw [hwordAppend, FiniteWeylWord.permEval_append,
      hSwapInv] at hStot
    exact mul_inv_eq_one.mp hStot
  calc
    _ = FiniteWeylWord.permEval word₁ :=
      (FiniteWeylWord.permEval_ofBoundedNat
        a₁ b₁ ha₁ hb₁ hab₁ u₁).symm
    _ = FiniteWeylWord.permEval word₂ := hpermEq
    _ = _ := FiniteWeylWord.permEval_ofBoundedNat
      a₂ b₂ ha₂ hb₂ hab₂ u₂

/-- Every finite-Weyl element admits a swap-product candidate. Purpose: public
representation-choice specification for `finiteWeylPerm`; it must be public
because the homomorphism's choice data cannot rest on a private lemma under
`@[expose]`. Nonclaim: no independence claim (see
`swapProd_eq_of_weylProd_eq`). -/
public theorem finiteWeylPerm_exists_repr (n : ℕ)
    (w : ↥(finiteWeylSubgroup (R := F) n)) :
    ∃ S : Equiv.Perm (Fin n), ∃ (m : ℕ) (a b : Fin m → ℕ)
      (ha : ∀ k, a k < n) (hb : ∀ k, b k < n) (hab : ∀ k, a k ≠ b k)
      (u : Fin m → Fˣ),
      (↑w : StableSteinberg F) =
        (List.ofFn fun k => weyl (R := F) (a k) (b k) (hab k) (u k)).prod ∧
      S = (List.ofFn fun k =>
        Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)).prod := by
  obtain ⟨m, a, b, ha, hb, hab, u, hW⟩ :=
    finiteWeylSubgroup_exists_list_repr (R := F) w.2
  exact ⟨_, m, a, b, ha, hb, hab, u, hW, rfl⟩

/-- Finite-Weyl permutation homomorphism: the head-left product of the
corresponding `Equiv.swap`s. Purpose: well-defined permutation of a finite
Weyl element for the Lemma-25 route. `Perm.mul_apply` is
`(σ * τ) i = σ (τ i)`, matching head-left `List.prod` on both sides.
Nonclaims: no Bruhat, quotient, or Matsumoto claim. -/
public noncomputable def finiteWeylPerm (n : ℕ) :
    ↥(finiteWeylSubgroup (R := F) n) →* Equiv.Perm (Fin n) where
  toFun w := Classical.choose (finiteWeylPerm_exists_repr (F := F) n w)
  map_one' := by
    have hW : ((1 : ↥(finiteWeylSubgroup (R := F) n)) : StableSteinberg F) =
        (List.ofFn fun k : Fin 0 => weyl (R := F)
          ((fun k => Fin.elim0 k) k) ((fun k => Fin.elim0 k) k)
          ((fun k => Fin.elim0 k) k) ((fun k => Fin.elim0 k) k)).prod := by
      simp
    obtain ⟨m₀, a₀, b₀, ha₀, hb₀, hab₀, u₀, hW₀, hS₀⟩ :=
      Classical.choose_spec (finiteWeylPerm_exists_repr (F := F) n 1)
    have h_eq : (List.ofFn fun k : Fin 0 => weyl (R := F)
        ((fun k => Fin.elim0 k) k) ((fun k => Fin.elim0 k) k)
        ((fun k => Fin.elim0 k) k) ((fun k => Fin.elim0 k) k)).prod =
        (List.ofFn fun k : Fin m₀ =>
          weyl (R := F) (a₀ k) (b₀ k) (hab₀ k) (u₀ k)).prod := by
      rw [← hW, ← hW₀]
    have hswap := swapProd_eq_of_weylProd_eq (F := F)
      (ha₁ := fun k : Fin 0 => Fin.elim0 k)
      (hb₁ := fun k : Fin 0 => Fin.elim0 k)
      (ha₂ := ha₀) (hb₂ := hb₀) h_eq
    change Classical.choose (finiteWeylPerm_exists_repr (F := F) n 1) = 1
    rw [hS₀]
    rw [← hswap]
    simp
  map_mul' := by
    intro x y
    obtain ⟨m₁, a₁, b₁, ha₁, hb₁, hab₁, u₁, hWx⟩ :=
      finiteWeylSubgroup_exists_list_repr (R := F) x.2
    obtain ⟨m₂, a₂, b₂, ha₂, hb₂, hab₂, u₂, hWy⟩ :=
      finiteWeylSubgroup_exists_list_repr (R := F) y.2
    have ha : ∀ k : Fin (m₁ + m₂), (Fin.append a₁ a₂) k < n := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]
        exact ha₁ i
      · rw [Fin.append_right]
        exact ha₂ i
    have hb : ∀ k : Fin (m₁ + m₂), (Fin.append b₁ b₂) k < n := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]
        exact hb₁ i
      · rw [Fin.append_right]
        exact hb₂ i
    have hab : ∀ k : Fin (m₁ + m₂),
        (Fin.append a₁ a₂) k ≠ (Fin.append b₁ b₂) k := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left, Fin.append_left]
        exact hab₁ i
      · rw [Fin.append_right, Fin.append_right]
        exact hab₂ i
    set hu : Fin (m₁ + m₂) → Fˣ := Fin.append u₁ u₂ with hu_def
    have hfunW : Fin.append
        (fun k : Fin m₁ => weyl (R := F) (a₁ k) (b₁ k) (hab₁ k) (u₁ k))
        (fun k : Fin m₂ => weyl (R := F) (a₂ k) (b₂ k) (hab₂ k) (u₂ k)) =
        fun k : Fin (m₁ + m₂) => weyl (R := F)
          ((Fin.append a₁ a₂) k) ((Fin.append b₁ b₂) k) (hab k) (hu k) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
        simp [Fin.append_left, Fin.append_right, hu_def]
    have hsplitW : (List.ofFn fun k : Fin (m₁ + m₂) => weyl (R := F)
        ((Fin.append a₁ a₂) k) ((Fin.append b₁ b₂) k) (hab k) (hu k)).prod =
        (List.ofFn fun k : Fin m₁ =>
          weyl (R := F) (a₁ k) (b₁ k) (hab₁ k) (u₁ k)).prod *
        (List.ofFn fun k : Fin m₂ =>
          weyl (R := F) (a₂ k) (b₂ k) (hab₂ k) (u₂ k)).prod := by
      rw [← List.prod_append, ← List.ofFn_fin_append, hfunW]
    have hWxy : ((x * y : ↥(finiteWeylSubgroup (R := F) n)) :
        StableSteinberg F) =
        (List.ofFn fun k : Fin (m₁ + m₂) => weyl (R := F)
          ((Fin.append a₁ a₂) k) ((Fin.append b₁ b₂) k) (hab k) (hu k)).prod := by
      have hcoe : ((x * y : ↥(finiteWeylSubgroup (R := F) n)) :
          StableSteinberg F) = (↑x : StableSteinberg F) * ↑y := rfl
      rw [hcoe, hWx, hWy, ← hsplitW]
    have hfunS : Fin.append
        (fun k : Fin m₁ =>
          Equiv.swap (⟨a₁ k, ha₁ k⟩ : Fin n) (⟨b₁ k, hb₁ k⟩ : Fin n))
        (fun k : Fin m₂ =>
          Equiv.swap (⟨a₂ k, ha₂ k⟩ : Fin n) (⟨b₂ k, hb₂ k⟩ : Fin n)) =
        fun k : Fin (m₁ + m₂) =>
          Equiv.swap (⟨(Fin.append a₁ a₂) k, ha k⟩ : Fin n)
            (⟨(Fin.append b₁ b₂) k, hb k⟩ : Fin n) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
        simp [Fin.append_left, Fin.append_right]
    have hsplitS : (List.ofFn fun k : Fin (m₁ + m₂) =>
        Equiv.swap (⟨(Fin.append a₁ a₂) k, ha k⟩ : Fin n)
          (⟨(Fin.append b₁ b₂) k, hb k⟩ : Fin n)).prod =
        (List.ofFn fun k : Fin m₁ =>
          Equiv.swap (⟨a₁ k, ha₁ k⟩ : Fin n) (⟨b₁ k, hb₁ k⟩ : Fin n)).prod *
        (List.ofFn fun k : Fin m₂ =>
          Equiv.swap (⟨a₂ k, ha₂ k⟩ : Fin n) (⟨b₂ k, hb₂ k⟩ : Fin n)).prod := by
      rw [← List.prod_append, ← List.ofFn_fin_append, hfunS]
    obtain ⟨mₓ, aₓ, bₓ, haₓ, hbₓ, habₓ, uₓ, hWₓ, hSₓ⟩ :=
      Classical.choose_spec (finiteWeylPerm_exists_repr (F := F) n x)
    obtain ⟨m_y, a_y, b_y, ha_y, hb_y, hab_y, u_y, hW_y, hS_y⟩ :=
      Classical.choose_spec (finiteWeylPerm_exists_repr (F := F) n y)
    obtain ⟨m_xy, a_xy, b_xy, ha_xy, hb_xy, hab_xy, u_xy, hW_xy, hS_xy⟩ :=
      Classical.choose_spec (finiteWeylPerm_exists_repr (F := F) n (x * y))
    have hx_eq : (List.ofFn fun k : Fin m₁ =>
        weyl (R := F) (a₁ k) (b₁ k) (hab₁ k) (u₁ k)).prod =
        (List.ofFn fun k : Fin mₓ =>
          weyl (R := F) (aₓ k) (bₓ k) (habₓ k) (uₓ k)).prod := by
      rw [← hWx, ← hWₓ]
    have hy_eq : (List.ofFn fun k : Fin m₂ =>
        weyl (R := F) (a₂ k) (b₂ k) (hab₂ k) (u₂ k)).prod =
        (List.ofFn fun k : Fin m_y =>
          weyl (R := F) (a_y k) (b_y k) (hab_y k) (u_y k)).prod := by
      rw [← hWy, ← hW_y]
    have hxy_eq : (List.ofFn fun k : Fin (m₁ + m₂) => weyl (R := F)
        ((Fin.append a₁ a₂) k) ((Fin.append b₁ b₂) k) (hab k) (hu k)).prod =
        (List.ofFn fun k : Fin m_xy =>
          weyl (R := F) (a_xy k) (b_xy k) (hab_xy k) (u_xy k)).prod := by
      rw [← hWxy, ← hW_xy]
    have hsx := swapProd_eq_of_weylProd_eq (F := F)
      (ha₁ := ha₁) (hb₁ := hb₁) (ha₂ := haₓ) (hb₂ := hbₓ) hx_eq
    have hsy := swapProd_eq_of_weylProd_eq (F := F)
      (ha₁ := ha₂) (hb₁ := hb₂) (ha₂ := ha_y) (hb₂ := hb_y) hy_eq
    have hsxy := swapProd_eq_of_weylProd_eq (F := F)
      (ha₁ := ha) (hb₁ := hb) (ha₂ := ha_xy) (hb₂ := hb_xy) hxy_eq
    change Classical.choose (finiteWeylPerm_exists_repr (F := F) n (x * y)) =
      Classical.choose (finiteWeylPerm_exists_repr (F := F) n x) *
        Classical.choose (finiteWeylPerm_exists_repr (F := F) n y)
    rw [hS_xy, hSₓ, hS_y, ← hsx, ← hsy, ← hsplitS, hsxy]

/-- Generator behavior actually needed downstream: the permutation of a
bounded Weyl generator is the corresponding `Equiv.swap`. Purpose: single-step
input for word conjugation. Hypotheses: `i < n`, `j < n`, `i ≠ j`.
Orientation: head-left singleton product. Nonclaim: no Bruhat or Matsumoto
claim. -/
public theorem finiteWeylPerm_weyl {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (u : Fˣ) :
    finiteWeylPerm (F := F) n
      ⟨weyl (R := F) i j hij u, weyl_mem_finiteWeylSubgroup hi hj hij u⟩ =
      Equiv.swap (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n) := by
  have hW : (weyl (R := F) i j hij u : StableSteinberg F) =
      (List.ofFn fun k : Fin 1 => weyl (R := F)
        ((fun _ => i) k) ((fun _ => j) k) ((fun _ => hij) k)
        ((fun _ => u) k)).prod := by
    simp
  obtain ⟨m₀, a₀, b₀, ha₀, hb₀, hab₀, u₀, hW₀, hS₀⟩ :=
    Classical.choose_spec (finiteWeylPerm_exists_repr (F := F) n
      ⟨weyl (R := F) i j hij u, weyl_mem_finiteWeylSubgroup hi hj hij u⟩)
  have h_eq : (List.ofFn fun k : Fin 1 => weyl (R := F)
      ((fun _ => i) k) ((fun _ => j) k) ((fun _ => hij) k)
      ((fun _ => u) k)).prod =
      (List.ofFn fun k : Fin m₀ =>
        weyl (R := F) (a₀ k) (b₀ k) (hab₀ k) (u₀ k)).prod := by
    rw [← hW, ← hW₀]
  have hswap := swapProd_eq_of_weylProd_eq (F := F)
    (ha₁ := fun _ => hi) (hb₁ := fun _ => hj) (ha₂ := ha₀) (hb₂ := hb₀) h_eq
  have hS : (List.ofFn fun k : Fin 1 =>
      Equiv.swap (⟨(fun _ => i) k, (fun _ => hi) k⟩ : Fin n)
        (⟨(fun _ => j) k, (fun _ => hj) k⟩ : Fin n)).prod =
      Equiv.swap (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n) := by
    simp
  change Classical.choose (finiteWeylPerm_exists_repr (F := F) n _) = _
  rw [hS₀, ← hS, hswap]

/-- A Weyl generator commutes with a disjoint root element: each of the three
`x`-factors of `weyl i j u` commutes with `x p q a` by `x_comm` when
`{i, j} ∩ {p, q} = ∅`. Purpose: disjoint case of single-generator
conjugation. Orientation: `weyl * x = x * weyl`. -/
private theorem weyl_comm_x_of_disjoint {i j p q : ℕ} (hij : i ≠ j)
    (hpq : p ≠ q) (hip : i ≠ p) (hiq : i ≠ q) (hjp : j ≠ p) (hjq : j ≠ q)
    (u : Fˣ) (a : F) :
    Commute (weyl (R := F) i j hij u) (x (R := F) p q hpq a) := by
  have h1 : Commute (x (R := F) i j hij (↑u : F))
      (x (R := F) p q hpq a) := by
    rw [commute_iff_eq]
    exact (commutatorElement_eq_one_iff_commute.mp
      (x_comm (R := F) i j p q hij hpq hiq hjp _ _)).eq
  have h2 : Commute (x (R := F) j i hij.symm (-(↑u⁻¹ : F)))
      (x (R := F) p q hpq a) := by
    rw [commute_iff_eq]
    exact (commutatorElement_eq_one_iff_commute.mp
      (x_comm (R := F) j i p q hij.symm hpq hjq hip _ _)).eq
  unfold weyl
  exact Commute.mul_left (Commute.mul_left h1 h2) h1

/-- Single-generator Weyl conjugation sends `x p q c` to the root at the
`Equiv.swap i j` images, with existential coefficient. Purpose: one-step input
for bounded-word conjugation. The proof is an exhaustive split: the two
diagonal cases use `weyl_conj_x_ij`/`weyl_conj_x_ji`, the four shared-index
cases use `weyl_conj_x_jk`/`weyl_conj_x_ik`/`weyl_conj_x_kj`/`weyl_conj_x_ki`,
and the disjoint case uses `weyl_comm_x_of_disjoint`. Index witnesses are
reconciled by proof irrelevance; the final index orientation is exact. -/
private theorem weyl_conj_x_single {n i j p q : ℕ} (hi : i < n) (hj : j < n)
    (hp : p < n) (hq : q < n) (hij : i ≠ j) (hpq : p ≠ q) (u : Fˣ) (c : F) :
    ∃ (c' : F),
      ∃ (h : ((Equiv.swap (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n)) ⟨p, hp⟩).val ≠
          ((Equiv.swap (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n)) ⟨q, hq⟩).val),
        weyl (R := F) i j hij u * x (R := F) p q hpq c *
            (weyl (R := F) i j hij u)⁻¹ =
          x (R := F) _ _ h c' := by
  set σ : Equiv.Perm (Fin n) :=
    Equiv.swap (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n) with hσ
  have hσi : σ ⟨i, hi⟩ = ⟨j, hj⟩ := by
    rw [hσ]
    exact Equiv.swap_apply_left _ _
  have hσj : σ ⟨j, hj⟩ = ⟨i, hi⟩ := by
    rw [hσ]
    exact Equiv.swap_apply_right _ _
  have hFinEq : ∀ {r : ℕ} (hr : r < n) (h : p = r),
      (⟨p, hp⟩ : Fin n) = ⟨r, hr⟩ := fun hr h => Fin.ext_iff.mpr h
  have hFinEqQ : ∀ {r : ℕ} (hr : r < n) (h : q = r),
      (⟨q, hq⟩ : Fin n) = ⟨r, hr⟩ := fun hr h => Fin.ext_iff.mpr h
  have hFinNe : ∀ {r : ℕ} (hr : r < n) (h : p ≠ r),
      (⟨p, hp⟩ : Fin n) ≠ ⟨r, hr⟩ := fun hr h he => h (congrArg Fin.val he)
  have hFinNeQ : ∀ {r : ℕ} (hr : r < n) (h : q ≠ r),
      (⟨q, hq⟩ : Fin n) ≠ ⟨r, hr⟩ := fun hr h he => h (congrArg Fin.val he)
  by_cases hpi : p = i
  · by_cases hqi : q = i
    · exfalso
      exact hpq (hpi.trans hqi.symm)
    · by_cases hqj : q = j
      · -- `p = i`, `q = j`: `weyl_conj_x_ij`.
        have eP : σ ⟨p, hp⟩ = ⟨j, hj⟩ := by
          rw [hFinEq hi hpi]
          exact hσi
        have eQ : σ ⟨q, hq⟩ = ⟨i, hi⟩ := by
          rw [hFinEqQ hj hqj]
          exact hσj
        have hconv : x (R := F) p q hpq c = x (R := F) i j hij c := by
          simp only [hpi, hqj]
        have htab := weyl_conj_x_ij (R := F) i j hij u c
        refine ⟨-((↑u⁻¹ : F) * c * (↑u⁻¹ : F)), by
          rw [eP, eQ]
          exact hij.symm, ?_⟩
        rw [hconv]
        simp only [eP, eQ]
        exact htab
      · -- `p = i`, `q` fresh: `weyl_conj_x_ik`.
        have hjq : j ≠ q := fun h => hqj h.symm
        have hiq : i ≠ q := fun h => hqi h.symm
        have eP : σ ⟨p, hp⟩ = ⟨j, hj⟩ := by
          rw [hFinEq hi hpi]
          exact hσi
        have eQ : σ ⟨q, hq⟩ = ⟨q, hq⟩ :=
          Equiv.swap_apply_of_ne_of_ne (hFinNeQ hi hqi) (hFinNeQ hj hqj)
        have hconv : x (R := F) p q hpq c = x (R := F) i q hiq c := by
          simp only [hpi]
        have htab := weyl_conj_x_ik (R := F) i j q hij hjq hiq u c
        refine ⟨-((↑u⁻¹ : F) * c), by rw [eP, eQ]; exact hjq, ?_⟩
        rw [hconv]
        simp only [eP, eQ]
        exact htab
  · by_cases hpj : p = j
    · by_cases hqi : q = i
      · -- `p = j`, `q = i`: `weyl_conj_x_ji`.
        have eP : σ ⟨p, hp⟩ = ⟨i, hi⟩ := by
          rw [hFinEq hj hpj]
          exact hσj
        have eQ : σ ⟨q, hq⟩ = ⟨j, hj⟩ := by
          rw [hFinEqQ hi hqi]
          exact hσi
        have hconv : x (R := F) p q hpq c = x (R := F) j i hij.symm c := by
          simp only [hpj, hqi]
        have htab := weyl_conj_x_ji (R := F) i j hij u c
        refine ⟨-((↑u : F) * c * (↑u : F)), by rw [eP, eQ]; exact hij, ?_⟩
        rw [hconv]
        simp only [eP, eQ]
        exact htab
      · by_cases hqj : q = j
        · exfalso
          exact hpq (hpj.trans hqj.symm)
        · -- `p = j`, `q` fresh: `weyl_conj_x_jk`.
          have hjq : j ≠ q := fun h => hqj h.symm
          have hiq : i ≠ q := fun h => hqi h.symm
          have eP : σ ⟨p, hp⟩ = ⟨i, hi⟩ := by
            rw [hFinEq hj hpj]
            exact hσj
          have eQ : σ ⟨q, hq⟩ = ⟨q, hq⟩ :=
            Equiv.swap_apply_of_ne_of_ne (hFinNeQ hi hqi) (hFinNeQ hj hqj)
          have hconv : x (R := F) p q hpq c = x (R := F) j q hjq c := by
            simp only [hpj]
          have htab := weyl_conj_x_jk (R := F) i j q hij hjq hiq u c
          refine ⟨((↑u : F) * c), by rw [eP, eQ]; exact hiq, ?_⟩
          rw [hconv]
          simp only [eP, eQ]
          exact htab
    · by_cases hqi : q = i
      · -- `p` fresh, `q = i`: `weyl_conj_x_ki`.
        have hip : i ≠ p := fun h => hpi h.symm
        have hjp : j ≠ p := fun h => hpj h.symm
        have eP : σ ⟨p, hp⟩ = ⟨p, hp⟩ :=
          Equiv.swap_apply_of_ne_of_ne (hFinNe hi hpi) (hFinNe hj hpj)
        have eQ : σ ⟨q, hq⟩ = ⟨j, hj⟩ := by
          rw [hFinEqQ hi hqi]
          exact hσi
        have hconv : x (R := F) p q hpq c = x (R := F) p i hip.symm c := by
          simp only [hqi]
        have htab := weyl_conj_x_ki (R := F) i j p hij hjp hip u c
        refine ⟨-(c * (↑u : F)), by rw [eP, eQ]; exact hpj, ?_⟩
        rw [hconv]
        simp only [eP, eQ]
        exact htab
      · by_cases hqj : q = j
        · -- `p` fresh, `q = j`: `weyl_conj_x_kj`.
          have hip : i ≠ p := fun h => hpi h.symm
          have hjp : j ≠ p := fun h => hpj h.symm
          have eP : σ ⟨p, hp⟩ = ⟨p, hp⟩ :=
            Equiv.swap_apply_of_ne_of_ne (hFinNe hi hpi) (hFinNe hj hpj)
          have eQ : σ ⟨q, hq⟩ = ⟨i, hi⟩ := by
            rw [hFinEqQ hj hqj]
            exact hσj
          have hconv : x (R := F) p q hpq c = x (R := F) p j hjp.symm c := by
            simp only [hqj]
          have htab := weyl_conj_x_kj (R := F) i j p hij hjp hip u c
          refine ⟨(c * (↑u⁻¹ : F)), by rw [eP, eQ]; exact hpi, ?_⟩
          rw [hconv]
          simp only [eP, eQ]
          exact htab
        · -- Disjoint indices: the Weyl generator commutes with the root.
          have hip : i ≠ p := fun h => hpi h.symm
          have hiq : i ≠ q := fun h => hqi h.symm
          have hjp : j ≠ p := fun h => hpj h.symm
          have hjq : j ≠ q := fun h => hqj h.symm
          have eP : σ ⟨p, hp⟩ = ⟨p, hp⟩ :=
            Equiv.swap_apply_of_ne_of_ne (hFinNe hi hpi) (hFinNe hj hpj)
          have eQ : σ ⟨q, hq⟩ = ⟨q, hq⟩ :=
            Equiv.swap_apply_of_ne_of_ne (hFinNeQ hi hqi) (hFinNeQ hj hqj)
          have hcomm :=
            weyl_comm_x_of_disjoint (F := F) hij hpq hip hiq hjp hjq u c
          have htab : weyl (R := F) i j hij u * x (R := F) p q hpq c *
              (weyl (R := F) i j hij u)⁻¹ = x (R := F) p q hpq c := by
            rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
          refine ⟨c, by rw [eP, eQ]; exact hpq, ?_⟩
          simp only [eP, eQ]
          exact htab

/-- Conjugation by a bundled head-left Weyl word sends `x p q c` to one
root element at the `permEval` images. The tail acts first and the head acts
outermost, exactly as in `FiniteWeylWord.permEval_cons`. -/
private theorem conj_ofFn_word_aux {n : ℕ}
    (word : FiniteWeylWord F (Fin n)) (p q : ℕ) (hp : p < n)
    (hq : q < n) (hpq : p ≠ q) (c : F) :
    ∃ (c' : F),
      ∃ (h : ((FiniteWeylWord.permEval word) ⟨p, hp⟩).val ≠
          ((FiniteWeylWord.permEval word) ⟨q, hq⟩).val),
        evalFiniteWeylWord word * x (R := F) p q hpq c *
            (evalFiniteWeylWord word)⁻¹ =
          x (R := F) _ _ h c' := by
  induction word with
  | nil =>
      exact ⟨c, by simpa using hpq, by simp⟩
  | cons letter word ih =>
      obtain ⟨c₁, h₁, e₁⟩ := ih
      obtain ⟨c₂, h₂, e₂⟩ := weyl_conj_x_single (F := F)
        letter.left.isLt letter.right.isLt
        ((FiniteWeylWord.permEval word ⟨p, hp⟩).isLt)
        ((FiniteWeylWord.permEval word ⟨q, hq⟩).isLt)
        (letterNatNe letter) h₁ letter.unit c₁
      refine ⟨c₂, ?_, ?_⟩
      · simpa only [FiniteWeylWord.permEval_cons, WeylLetter.perm,
          Equiv.Perm.mul_apply] using h₂
      · rw [evalFiniteWeylWord_cons]
        calc
          (evalLetter letter * evalFiniteWeylWord word) *
                x (R := F) p q hpq c *
              (evalLetter letter * evalFiniteWeylWord word)⁻¹ =
            evalLetter letter *
                (evalFiniteWeylWord word * x (R := F) p q hpq c *
                  (evalFiniteWeylWord word)⁻¹) *
              (evalLetter letter)⁻¹ := by
                rw [mul_inv_rev]
                simp only [mul_assoc]
          _ = evalLetter letter * x (R := F) _ _ h₁ c₁ *
                (evalLetter letter)⁻¹ := by rw [e₁]
          _ = _ := by
            simpa only [evalLetter, FiniteWeylWord.permEval_cons,
              WeylLetter.perm, Equiv.Perm.mul_apply] using e₂

/-- Reusable bounded-word conjugation: conjugating `x p q c` by a finite-Weyl
element yields one root element whose indices are the induced permutation
images. Purpose: word-level transport input for Lemma-25 double-coset
arguments. Hypotheses: `p < n`, `q < n`, `p ≠ q`. Orientation: conjugation is
`w * y * w⁻¹` with the conjugator on the left; indices are
`((finiteWeylPerm n w) ⟨p, hp⟩).val` and likewise for `q`. Coefficients
remain existential; the index orientation is exact. Nonclaim: no Bruhat,
quotient, or Matsumoto claim. -/
public theorem finiteWeyl_conj_x (n : ℕ) (w : ↥(finiteWeylSubgroup (R := F) n))
    {p q : ℕ} (hp : p < n) (hq : q < n) (hpq : p ≠ q) (c : F) :
    ∃ (c' : F),
      ∃ (h : ((finiteWeylPerm (F := F) n w) ⟨p, hp⟩).val ≠
          ((finiteWeylPerm (F := F) n w) ⟨q, hq⟩).val),
        (↑w : StableSteinberg F) * x (R := F) p q hpq c * (↑w)⁻¹ =
          x (R := F) _ _ h c' := by
  obtain ⟨m₀, a₀, b₀, ha₀, hb₀, hab₀, u₀, hW₀, hS₀⟩ :=
    Classical.choose_spec (finiteWeylPerm_exists_repr (F := F) n w)
  let word := FiniteWeylWord.ofBoundedNat a₀ b₀ ha₀ hb₀ hab₀ u₀
  obtain ⟨c', h', e'⟩ :=
    conj_ofFn_word_aux (F := F) word p q hp hq hpq c
  have hperm : finiteWeylPerm (F := F) n w =
      FiniteWeylWord.permEval word :=
    hS₀.trans
      (FiniteWeylWord.permEval_ofBoundedNat
        a₀ b₀ ha₀ hb₀ hab₀ u₀).symm
  have hW : (↑w : StableSteinberg F) = evalFiniteWeylWord word :=
    hW₀.trans
      (evalFiniteWeylWord_ofBoundedNat a₀ b₀ ha₀ hb₀ hab₀ u₀).symm
  refine ⟨c', by simpa only [hperm] using h', ?_⟩
  simpa only [hW, ← hperm] using e'

/-- Positive simple-root transport: for `hm : m + 1 < n`, a finite-Weyl
element `w`, and positivity of its induced permutation on `m, m + 1`, every
`w * g * w⁻¹` with `g ∈ simpleRootSubgroup m` lies in
`finiteBorelSubgroup n`. Purpose: reusable Lemma-25 prerequisite sending the
simple root into the finite Borel. The proof eliminates `g` to one
`x m (m + 1)` generator via `simpleRootSubgroup_exists_eq_x`, conjugates by
`finiteWeyl_conj_x`, and lands in the upper subgroup (hence the Borel) since
positivity gives the strict index inequality. Nonclaim: no complement,
quotient, Bruhat, or Matsumoto claim. -/
public theorem finiteWeyl_simpleRoot_mem_borel {n m : ℕ} (hm : m + 1 < n)
    (w : ↥(finiteWeylSubgroup (R := F) n))
    (hpos : ((finiteWeylPerm (F := F) n w) ⟨m, Nat.lt_of_succ_lt hm⟩).val <
      ((finiteWeylPerm (F := F) n w) ⟨m + 1, hm⟩).val)
    {g : StableSteinberg F} (hg : g ∈ simpleRootSubgroup (F := F) m) :
    (↑w : StableSteinberg F) * g * (↑w)⁻¹ ∈ finiteBorelSubgroup (F := F) n := by
  obtain ⟨a, rfl⟩ := simpleRootSubgroup_exists_eq_x (F := F) m hg
  have hp : m < n := Nat.lt_of_succ_lt hm
  have hpq : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  obtain ⟨c', h', e'⟩ := finiteWeyl_conj_x (F := F) n w hp hm hpq a
  rw [e']
  exact upperUnipotentSubgroup_le_finiteBorelSubgroup (F := F) n
    (x_mem_upperUnipotentSubgroup (R := F) h' hpos
      (finiteWeylPerm (F := F) n w ⟨m, hp⟩).isLt
      (finiteWeylPerm (F := F) n w ⟨m + 1, hm⟩).isLt c')

end StableSteinberg

end AlgebraicKTheory

end
