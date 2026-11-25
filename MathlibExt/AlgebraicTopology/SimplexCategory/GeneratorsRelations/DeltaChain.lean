/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.EpiMono

@[expose] public section

/-! # Indexed face chains for the `P_δ` normal form

`DeltaChain n m` stores a composite of `m - n` face maps `δ` with `Fin`
indices and target degrees carried definitionally in the type. `Admissible`
selects the strictly increasing normal form and `normalize` sorts an arbitrary
chain by insertion, preserving evaluation. Indexing the endpoints keeps all
`eqToHom` transports at the boundary and avoids internal `Fin.ofNat`
reconstructions. -/

namespace SimplexCategoryGenRel

open CategoryTheory

/--
Indexed face chain for the `P_δ` normal form.

`DeltaChain n m` represents a composite of `m - n` face maps `δ` from `mk n` to `mk m`. The
constructors store `Fin` indices and target degrees definitionally, eliminating internal `eqToHom`
and `Fin.ofNat`.

Insertion-sort normalization gives an admissible strictly increasing face chain.
-/
inductive DeltaChain (n : ℕ) : ℕ → Type
  | nil : DeltaChain n n
  | snoc {m : ℕ} : DeltaChain n m → Fin (m + 2) → DeltaChain n (m + 1)

namespace DeltaChain

variable {n : ℕ}

/--
Evaluation of a `DeltaChain` as a morphism `mk n ⟶ mk m` in
`SimplexCategoryGenRel`. `nil` is the identity and `snoc` composes by
the delta generator `δ`.
-/
def eval : {m : ℕ} → DeltaChain n m → (mk n ⟶ mk m)
  | _, .nil => 𝟙 (mk n)
  | _, .snoc c i => c.eval ≫ δ i

@[simp]
theorem eval_nil : (nil (n := n)).eval = 𝟙 (mk n) := rfl
@[simp, reassoc]
theorem eval_snoc {m : ℕ} (c : DeltaChain n m) (i : Fin (m + 2)) :
    (c.snoc i).eval = c.eval ≫ δ i :=
  rfl

/-- Every `DeltaChain` evaluates to a `P_δ` morphism (composite of `δ`s). -/
theorem eval_mem_P_delta {n : ℕ} {m : ℕ} (c : DeltaChain n m) : P_δ c.eval := by
  induction c with
  | nil => simpa [eval] using P_δ.id_mem (mk n)
  | snoc c i ih => simpa [eval] using P_δ.comp_mem _ _ ih (P_δ.δ i)

/--
Structural monotonicity: `n ≤ m` for any `DeltaChain n m`.
The indexed type already encodes this definitionally via construction,
but the inequality is convenient for downstream lemmas.
-/
theorem le {n m : ℕ} (c : DeltaChain n m) : n ≤ m := by
  induction c with
  | nil => exact Nat.le_refl _
  | snoc _ _ ih => exact Nat.le_succ_of_le ih

/--
Append two indexed face chains. This concatenates the underlying
composites of face maps. The equations for `nil` and `snoc` are
transparent by definition.
-/
def append {m k : ℕ} (c₁ : DeltaChain n m) (c₂ : DeltaChain m k) :
    DeltaChain n k :=
  match c₂ with
  | .nil => c₁
  | .snoc c₂' i => (c₁.append c₂').snoc i

@[simp]
theorem append_nil {m : ℕ} (c : DeltaChain n m) :
    c.append (DeltaChain.nil (n := m)) = c := rfl

@[simp]
theorem append_snoc {m k : ℕ} (c₁ : DeltaChain n m) (c₂ : DeltaChain m k)
    (i : Fin (k + 2)) :
    c₁.append (c₂.snoc i) = (c₁.append c₂).snoc i := rfl

/-- Evaluation of `append` is composition of evaluations. -/
@[reassoc]
theorem eval_append {m k : ℕ} (c₁ : DeltaChain n m) (c₂ : DeltaChain m k) :
    (c₁.append c₂).eval = c₁.eval ≫ c₂.eval := by
  induction c₂ with
  | nil => simp [append, eval]
  | snoc c₂' i ih => simp [append, eval, ih]

/--
Evaluated order-preserving map of a face chain in `SimplexCategory`.

For `c : DeltaChain n m`, this is `(toSimplexCategory.map c.eval).toOrderHom`,
viewed as an order-homomorphism `Fin (n+1) →o Fin (m+1)`.
-/
def evalOrderHom {n₁ m₁ : ℕ} (c : DeltaChain n₁ m₁) :
    Fin (n₁ + 1) →o Fin (m₁ + 1) :=
  (toSimplexCategory.map c.eval).toOrderHom

@[simp]
theorem evalOrderHom_nil {n : ℕ} :
    evalOrderHom (DeltaChain.nil (n := n)) = OrderHom.id := by
  unfold evalOrderHom
  simp [eval]

@[simp]
theorem evalOrderHom_snoc {m : ℕ} (c : DeltaChain n m) (i : Fin (m + 2)) :
    evalOrderHom (c.snoc i) =
      (Fin.succAboveOrderEmb i).toOrderHom.comp (evalOrderHom c) := by
  unfold evalOrderHom
  rw [eval_snoc, Functor.map_comp, SimplexCategory.comp_toOrderHom]
  have h : (toSimplexCategory.map (δ i)).toOrderHom =
      (Fin.succAboveOrderEmb i).toOrderHom := by
    rw [toSimplexCategory_map_δ]
    rfl
  rw [h]
  rfl

theorem evalOrderHom_snoc_apply {m : ℕ} (c : DeltaChain n m) (i : Fin (m + 2))
    (a : Fin (n + 1)) :
    evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) := by
  have h : evalOrderHom (c.snoc i) =
      (Fin.succAboveOrderEmb i).toOrderHom.comp (evalOrderHom c) := evalOrderHom_snoc c i
  calc evalOrderHom (c.snoc i) a
      = ((Fin.succAboveOrderEmb i).toOrderHom.comp (evalOrderHom c)) a := by rw [← h]
    _ = (Fin.succAboveOrderEmb i) (evalOrderHom c a) := rfl
    _ = i.succAbove (evalOrderHom c a) := rfl

theorem mem_range_evalOrderHom_snoc_iff {m : ℕ} (c : DeltaChain n m)
    (i : Fin (m + 2)) (y : Fin (m + 2)) :
    y ∈ Set.range (evalOrderHom (c.snoc i)) ↔
      ∃ x ∈ Set.range (evalOrderHom c), i.succAbove x = y := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨evalOrderHom c a, ⟨a, rfl⟩, ?_⟩
    have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
      evalOrderHom_snoc_apply c i a
    rw [h_eq] at ha
    exact ha
  · rintro ⟨x, ⟨a, rfl⟩, hx⟩
    refine ⟨a, ?_⟩
    have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
      evalOrderHom_snoc_apply c i a
    rw [h_eq, hx]

theorem not_mem_range_evalOrderHom_snoc {m : ℕ} (c : DeltaChain n m)
    (i : Fin (m + 2)) : i ∉ Set.range (evalOrderHom (c.snoc i)) := by
  intro h
  obtain ⟨a, ha⟩ := h
  have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
    evalOrderHom_snoc_apply c i a
  rw [h_eq] at ha
  exact Fin.succAbove_ne i (evalOrderHom c a) ha

theorem mem_range_evalOrderHom_snoc_of_lt {m : ℕ} (c : DeltaChain n m)
    (i : Fin (m + 2)) (j : Fin (m + 2)) (h : j < i) :
    j ∈ Set.range (evalOrderHom (c.snoc i)) ↔
      (j.castPred (Fin.ne_last_of_lt (Fin.lt_of_lt_of_le h i.le_last))) ∈
        Set.range (evalOrderHom c) := by
  let hj : j ≠ Fin.last (m + 1) :=
    Fin.ne_last_of_lt (Fin.lt_of_lt_of_le h i.le_last)
  have h_succ : i.succAbove (j.castPred hj) = j := by
    have h_eq : j.castPred hj =
        j.castPred (Fin.ne_of_lt (Nat.lt_of_lt_of_le h i.le_last)) := by
      apply Fin.ext; rfl
    rw [h_eq]
    exact Fin.succAbove_castPred_of_lt i j h
  constructor
  · rintro ⟨a, ha⟩
    have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
      evalOrderHom_snoc_apply c i a
    rw [h_eq] at ha
    have h_inj : evalOrderHom c a = j.castPred hj := by
      apply Fin.succAbove_right_injective (p := i)
      rw [ha, h_succ]
    exact ⟨a, h_inj⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
      evalOrderHom_snoc_apply c i a
    rw [h_eq, ha, h_succ]

theorem mem_range_evalOrderHom_snoc_castPred_iff_of_lt {m : ℕ} (c : DeltaChain n m)
    (i : Fin (m + 2)) (j : Fin (m + 2)) (h : j < i) :
    j ∈ Set.range (evalOrderHom (c.snoc i)) ↔
      (j.castPred (Fin.ne_last_of_lt (Fin.lt_of_lt_of_le h i.le_last))) ∈
        Set.range (evalOrderHom c) :=
  mem_range_evalOrderHom_snoc_of_lt c i j h

theorem mem_range_evalOrderHom_snoc_of_gt {m : ℕ} (c : DeltaChain n m)
    (i : Fin (m + 2)) (j : Fin (m + 2)) (h : i < j) :
    j ∈ Set.range (evalOrderHom (c.snoc i)) ↔
      (j.pred (Fin.ne_zero_of_lt h)) ∈ Set.range (evalOrderHom c) := by
  let hj : j ≠ (0 : Fin (m + 2)) := Fin.ne_zero_of_lt h
  have h_succ : i.succAbove (j.pred hj) = j := by
    have h_eq : j.pred hj =
        j.pred (Fin.ne_of_gt (Fin.lt_of_le_of_lt (Fin.zero_le i) h)) := by
      apply Fin.ext; rfl
    rw [h_eq]
    exact Fin.succAbove_pred_of_lt i j h
  constructor
  · rintro ⟨a, ha⟩
    have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
      evalOrderHom_snoc_apply c i a
    rw [h_eq] at ha
    have h_inj : evalOrderHom c a = j.pred hj := by
      apply Fin.succAbove_right_injective (p := i)
      rw [ha, h_succ]
    exact ⟨a, h_inj⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h_eq : evalOrderHom (c.snoc i) a = i.succAbove (evalOrderHom c a) :=
      evalOrderHom_snoc_apply c i a
    rw [h_eq, ha, h_succ]

theorem mem_range_evalOrderHom_snoc_pred_iff_of_gt {m : ℕ} (c : DeltaChain n m)
    (i : Fin (m + 2)) (j : Fin (m + 2)) (h : i < j) :
    j ∈ Set.range (evalOrderHom (c.snoc i)) ↔
      (j.pred (Fin.ne_zero_of_lt h)) ∈ Set.range (evalOrderHom c) :=
  mem_range_evalOrderHom_snoc_of_gt c i j h

/--
Homogeneous natural-number list of the stored face indices, in stored order.
`nil` maps to `[]` and `snoc c i` maps to `c.toNatList ++ [i.val]`.
-/
def toNatList : {m : ℕ} → DeltaChain n m → List ℕ
  | _, .nil => []
  | _, .snoc c i => c.toNatList ++ [i.val]

@[simp]
theorem toNatList_nil : (nil (n := n)).toNatList = [] :=
  rfl

@[simp]
theorem toNatList_snoc {m : ℕ} (c : DeltaChain n m) (i : Fin (m + 2)) :
    (c.snoc i).toNatList = c.toNatList ++ [i.val] :=
  rfl

/-- Length statement: `n + |toNatList c| = m`. -/
theorem toNatList_length {m : ℕ} (c : DeltaChain n m) :
    n + c.toNatList.length = m := by
  induction c with
  | nil =>
    simp [toNatList]
  | snoc c _ ih =>
    simp only [toNatList, List.length_append, List.length_singleton] at *
    omega

/-- Subtraction corollary: `|toNatList c| = m - n`. -/
theorem toNatList_length_eq {m : ℕ} (c : DeltaChain n m) :
    c.toNatList.length = m - n := by
  have h := toNatList_length c
  omega

private theorem append_singleton_inj {α : Type*} {l₁ l₂ : List α} {a b : α}
    (h : l₁ ++ [a] = l₂ ++ [b]) : l₁ = l₂ ∧ a = b := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp only [List.nil_append] at h
    cases l₂ with
    | nil =>
      simpa using h
    | cons y ys =>
      have hlen : (y :: ys ++ [b]).length = 1 := by
        rw [← h]
        rfl
      simp [List.length_append] at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      simp only [List.nil_append] at h
      have hlen : (x :: xs ++ [a]).length = 1 := by
        rw [h]
        rfl
      simp [List.length_append] at hlen
    | cons y ys =>
      have eq1 : (x :: xs) ++ [a] = x :: (xs ++ [a]) := rfl
      have eq2 : (y :: ys) ++ [b] = y :: (ys ++ [b]) := rfl
      have h' : x :: (xs ++ [a]) = y :: (ys ++ [b]) := by
        rw [← eq1, ← eq2]
        exact h
      have hx : x = y := by
        injection h'
      have htail : xs ++ [a] = ys ++ [b] := by
        injection h'
      have ih_res := ih htail
      constructor
      · rw [hx, ih_res.1]
      · exact ih_res.2

/--
Fixed-endpoint injectivity of `toNatList`: equality of the stored natural-number lists
implies equality of the chains.
-/
theorem eq_of_toNatList_eq {m : ℕ} {c d : DeltaChain n m}
    (h : c.toNatList = d.toNatList) : c = d := by
  induction c with
  | nil =>
    cases d with
    | nil => rfl
    | snoc d' j =>
      simp only [toNatList] at h
      have hlen : (d'.toNatList ++ [j.val]).length = 0 := by
        rw [← h]
        rfl
      simp [List.length_append] at hlen
  | snoc c' i ih =>
    cases d with
    | nil =>
      simp only [toNatList] at h
      have hlen : (c'.toNatList ++ [i.val]).length = 0 := by
        rw [h]
        rfl
      simp [List.length_append] at hlen
    | snoc d' j =>
      simp only [toNatList] at h
      have h_inj := append_singleton_inj h
      have hc_eq : c' = d' := ih h_inj.1
      have hi_eq : i = j := Fin.ext h_inj.2
      rw [hc_eq, hi_eq]

/--
Source-general existence: a `P_δ` morphism from an arbitrary source
that is known to be `mk n` is represented by a `DeltaChain n m` up to
outer `eqToHom` transports. The proof is by direct induction on the
`multiplicativeClosure` witness for `P_δ`, using `snoc` for the face
step and keeping all transports at the boundary.
-/
theorem exists_chain_of_P_delta {x y : SimplexCategoryGenRel}
    (f : x ⟶ y) (hf : P_δ f) {n : ℕ} (hx : x = mk n) :
    ∃ m, ∃ (hy : y = mk m), ∃ (c : DeltaChain n m),
      c.eval = eqToHom hx.symm ≫ f ≫ eqToHom hy := by
  induction hf generalizing n with
  | of _ hf =>
    cases hf with
    | @δ n₀ i =>
      cases hx
      refine ⟨n + 1, rfl, (DeltaChain.nil (n := n)).snoc i, ?_⟩
      simp [eval]
  | id x =>
    cases hx
    refine ⟨n, rfl, DeltaChain.nil, ?_⟩
    simp [eval]
  | comp_of f g _ hg ih =>
    cases hg with
    | @δ a i =>
      obtain ⟨m₁, hy₁, c₁, hc₁⟩ := ih hx
      cases hy₁
      simp at hc₁
      refine ⟨a + 1, rfl, c₁.snoc i, ?_⟩
      simp [eval, hc₁]

/--
Source-fixed corollary: `f : mk n ⟶ y` with `P_δ f` is a chain up to
a final target transport.
-/
theorem exists_chain_mk_of_P_delta {n : ℕ} {y : SimplexCategoryGenRel}
    (f : mk n ⟶ y) (hf : P_δ f) :
    ∃ m, ∃ (hy : y = mk m), ∃ (c : DeltaChain n m),
      c.eval = f ≫ eqToHom hy := by
  obtain ⟨m, hy, c, hc⟩ := exists_chain_of_P_delta f hf rfl
  refine ⟨m, hy, c, ?_⟩
  simpa [eqToHom_refl] using hc

/--
Canonical-target corollary: a `P_δ` morphism between canonical
simplices is exactly a chain evaluation.
-/
theorem exists_chain_mk_mk_of_P_delta {n m : ℕ}
    (f : mk n ⟶ mk m) (hf : P_δ f) :
    ∃ c : DeltaChain n m, c.eval = f := by
  obtain ⟨m', hy, c, hc⟩ := exists_chain_mk_of_P_delta f hf
  have hm : m' = m := by
    have := congrArg len hy
    simpa [mk_len] using this.symm
  subst hm
  cases hy
  exact ⟨c, by simpa [eqToHom_refl] using hc⟩

/-- Admissible face chain: indices are strictly increasing. -/
inductive Admissible {n : ℕ} : {m : ℕ} → DeltaChain n m → Prop
  | nil : Admissible (n := n) (m := n) DeltaChain.nil
  | singleton {i : Fin (n + 2)} :
      Admissible ((DeltaChain.nil (n := n)).snoc i)
  | cons {m : ℕ} {c : DeltaChain n m} {j : Fin (m + 2)} {i : Fin (m + 3)}
      (h : Admissible (c.snoc j)) (hlt : j.val < i.val) :
      Admissible ((c.snoc j).snoc i)

/-- The underlying chain of an admissible `snoc` is admissible. -/
theorem Admissible.of_snoc {n m : ℕ} {c : DeltaChain n m} {j : Fin (m + 2)}
    (h : Admissible (c.snoc j)) : Admissible c := by
  cases h with
  | singleton => exact .nil
  | cons h _ => exact h

/-- All face indices of the chain are `< b`. -/
def AllValsLt {n : ℕ} : {m : ℕ} → DeltaChain n m → ℕ → Prop
  | _, .nil, _ => True
  | _, .snoc c i, b => AllValsLt c b ∧ i.val < b

/-- All face indices of the chain are `≤ b`. -/
def AllValsLe {n : ℕ} : {m : ℕ} → DeltaChain n m → ℕ → Prop
  | _, .nil, _ => True
  | _, .snoc c i, b => AllValsLe c b ∧ i.val ≤ b

/-- Monotonicity of `AllValsLt` in the bound. -/
theorem AllValsLt_mono {n : ℕ} {m : ℕ} (c : DeltaChain n m) {b b' : ℕ}
    (h : AllValsLt c b) (hle : b ≤ b') : AllValsLt c b' := by
  induction c generalizing b b' with
  | nil => trivial
  | snoc c₀ j ih =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨ih h₁ hle, Nat.lt_of_lt_of_le h₂ hle⟩

/-- Monotonicity of `AllValsLe` in the bound. -/
theorem AllValsLe_mono {n : ℕ} {m : ℕ} (c : DeltaChain n m) {b b' : ℕ}
    (h : AllValsLe c b) (hle : b ≤ b') : AllValsLe c b' := by
  induction c generalizing b b' with
  | nil => trivial
  | snoc c₀ j ih =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨ih h₁ hle, Nat.le_trans h₂ hle⟩

/-- `AllValsLt` implies `AllValsLe`. -/
theorem AllValsLt_le {n : ℕ} {m : ℕ} (c : DeltaChain n m) {b : ℕ}
    (h : AllValsLt c b) : AllValsLe c b := by
  induction c with
  | nil => trivial
  | snoc c₀ j ih =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨ih h₁, Nat.le_of_lt h₂⟩

/-- `AllValsLt` iff every member of `toNatList` is `< b`. -/
theorem AllValsLt_iff_forall_mem_lt {n : ℕ} {m : ℕ} {c : DeltaChain n m} {b : ℕ} :
    AllValsLt c b ↔ ∀ x ∈ c.toNatList, x < b := by
  induction c generalizing b with
  | nil =>
    simp [toNatList, AllValsLt]
  | snoc c i ih =>
    simp only [AllValsLt, toNatList]
    constructor
    · rintro ⟨hc, hi⟩ y hy
      rcases List.mem_append.mp hy with hmem | hmem
      · exact ih.mp hc y hmem
      · rw [List.mem_singleton.mp hmem]
        exact hi
    · intro h
      constructor
      · exact ih.mpr (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
      · exact h i.val
          (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

/-- `AllValsLe` iff every member of `toNatList` is `≤ b`. -/
theorem AllValsLe_iff_forall_mem_le {n : ℕ} {m : ℕ} {c : DeltaChain n m} {b : ℕ} :
    AllValsLe c b ↔ ∀ x ∈ c.toNatList, x ≤ b := by
  induction c generalizing b with
  | nil =>
    simp [toNatList, AllValsLe]
  | snoc c i ih =>
    simp only [AllValsLe, toNatList]
    constructor
    · rintro ⟨hc, hi⟩ y hy
      rcases List.mem_append.mp hy with hmem | hmem
      · exact ih.mp hc y hmem
      · rw [List.mem_singleton.mp hmem]
        exact hi
    · intro h
      constructor
      · exact ih.mpr (fun x hx => h x (List.mem_append.mpr (Or.inl hx)))
      · exact h i.val
          (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

/-- Forward corollary: `AllValsLt` implies all `toNatList` members `< b`. -/
theorem AllValsLt_forall_mem_lt {n : ℕ} {m : ℕ} {c : DeltaChain n m} {b : ℕ}
    (h : AllValsLt c b) : ∀ x ∈ c.toNatList, x < b :=
  (AllValsLt_iff_forall_mem_lt.mp h)

/-- Forward corollary: `AllValsLe` implies all `toNatList` members `≤ b`. -/
theorem AllValsLe_forall_mem_le {n : ℕ} {m : ℕ} {c : DeltaChain n m} {b : ℕ}
    (h : AllValsLe c b) : ∀ x ∈ c.toNatList, x ≤ b :=
  (AllValsLe_iff_forall_mem_le.mp h)

/-- Every stored index of a chain is `< m + 1`. In particular `AllValsLt c (m + 1)`. -/
theorem toNatList_allValsLt {n m : ℕ} (c : DeltaChain n m) :
    AllValsLt c (m + 1) := by
  induction c with
  | nil =>
    trivial
  | snoc c₀ j ih =>
    refine ⟨AllValsLt_mono c₀ ih (Nat.le_succ _), j.is_lt⟩

/-- Membership in `toNatList` implies `< m + 1`. -/
theorem mem_toNatList_lt {n m : ℕ} {c : DeltaChain n m} {x : ℕ}
    (hx : x ∈ c.toNatList) : x < m + 1 := by
  exact (AllValsLt_iff_forall_mem_lt.mp (toNatList_allValsLt c) x hx)

/-- An admissible `snoc` has all earlier indices `<` its last index. -/
theorem Admissible.allValsLt_of_snoc {n : ℕ} {m : ℕ} {c : DeltaChain n m}
    {j : Fin (m + 2)} (h : Admissible (c.snoc j)) :
    AllValsLt c j.val := by
  induction c with
  | nil => trivial
  | @snoc k c₀ k' ih =>
    cases h with
    | cons h₀ hlt =>
      have ih' : AllValsLt c₀ k'.val := ih h₀
      exact ⟨AllValsLt_mono c₀ ih' (Nat.le_of_lt hlt), hlt⟩

/-- Extend an admissible chain by an index larger than a `≤` bound on its values. -/
theorem Admissible.snoc_of_le_lt {n : ℕ} {m : ℕ} {c : DeltaChain n m}
    (hc : Admissible c) {B : ℕ} (hB : AllValsLe c B) {i : Fin (m + 2)}
    (hi : B < i.val) : Admissible (c.snoc i) := by
  cases c with
  | nil => exact .singleton
  | @snoc k c' j =>
    have hj_le : j.val ≤ B := hB.2
    have hj_lt : j.val < i.val := Nat.lt_of_le_of_lt hj_le hi
    exact .cons hc hj_lt

/-- Insert a face index into a chain, preserving semantics via the simplicial `δ` commutation. -/
def insert {n : ℕ} : {m : ℕ} → DeltaChain n m → Fin (m + 2) → DeltaChain n (m + 1)
  | _, .nil, i => DeltaChain.snoc (DeltaChain.nil (n := n)) i
  | _, .snoc (m := k) c₀ j, i =>
    if h : j.val < i.val then
      DeltaChain.snoc (DeltaChain.snoc c₀ j) i
    else
      have hi : i.val < k + 2 := by
        have hj : j.val < k + 2 := j.is_lt
        omega
      DeltaChain.snoc (insert c₀ (Fin.mk i.val hi)) (Fin.succ j)

/-- `insert` evaluates as appending `δ i` to the chain. -/
theorem insert_eval {n m : ℕ} (c : DeltaChain n m) (i : Fin (m + 2)) :
    (insert c i).eval = c.eval ≫ δ i := by
  induction c with
  | nil => rfl
  | @snoc k c₀ j ih =>
    dsimp only [insert]
    by_cases hlt : j.val < i.val
    · simp [hlt]
    · simp only [hlt]
      have hi_lt : i.val < k + 2 := by
        have := j.is_lt
        omega
      let i' : Fin (k + 2) := Fin.mk i.val hi_lt
      have hi_eq : i'.castSucc = i := by
        apply Fin.ext
        simp [i']
      have hj_le : i' ≤ j := by
        simp [Fin.le_def, i']
        omega
      calc
        (DeltaChain.snoc (insert c₀ i') (Fin.succ j)).eval
            = (insert c₀ i').eval ≫ δ (Fin.succ j) := rfl
        _ = (c₀.eval ≫ δ i') ≫ δ (Fin.succ j) := by rw [ih]
        _ = c₀.eval ≫ (δ i' ≫ δ (Fin.succ j)) := by rw [Category.assoc]
        _ = c₀.eval ≫ (δ j ≫ δ i) := by rw [δ_comp_δ hj_le, hi_eq]
        _ = (c₀.eval ≫ δ j) ≫ δ i := by rw [← Category.assoc]
        _ = (DeltaChain.snoc c₀ j).eval ≫ δ i := rfl

/--
`insert` preserves a `≤` bound when the inserted index
is `≤` a strict upper bound of the chain.
-/
theorem insert_allValsLe {n : ℕ} {m : ℕ} {c : DeltaChain n m}
    (hc : Admissible c) {B : ℕ} (hB : AllValsLt c B)
    (i : Fin (m + 2)) (hi : i.val ≤ B) :
    AllValsLe (insert c i) B := by
  induction c generalizing B with
  | nil =>
    simp only [insert]
    exact ⟨trivial, hi⟩
  | @snoc k c₀ j ih =>
    have hc_snoc : Admissible (c₀.snoc j) := hc
    have hc₀ : Admissible c₀ := hc_snoc.of_snoc
    have hB₀ : AllValsLt c₀ B := hB.1
    have hj_lt_B : j.val < B := hB.2
    have hB₀_j : AllValsLt c₀ j.val := hc_snoc.allValsLt_of_snoc
    dsimp only [insert]
    by_cases hlt : j.val < i.val
    · simp only [hlt]
      constructor
      · constructor
        · exact AllValsLt_le _ hB₀
        · exact Nat.le_of_lt hj_lt_B
      · exact hi
    · simp only [hlt]
      have hi_lt_k : i.val < k + 2 := by
        have := j.is_lt
        omega
      let i' : Fin (k + 2) := Fin.mk i.val hi_lt_k
      have hi'_le_j : i'.val ≤ j.val := by
        simp [i']
        omega
      have ih_le : AllValsLe (insert c₀ i') j.val :=
        ih hc₀ hB₀_j i' hi'_le_j
      have hj_succ_le : (Fin.succ j).val ≤ B := by
        simp [Fin.val_succ]
        omega
      constructor
      · exact AllValsLe_mono _ ih_le (Nat.le_of_lt hj_lt_B)
      · exact hj_succ_le

/-- Insertion preserves admissibility. -/
theorem insert_admissible {n : ℕ} {m : ℕ} {c : DeltaChain n m}
    (hc : Admissible c) (i : Fin (m + 2)) :
    Admissible (insert c i) := by
  induction c with
  | nil =>
    simp only [insert]
    exact .singleton
  | @snoc k c₀ j ih =>
    have hc_snoc : Admissible (c₀.snoc j) := hc
    have hc₀ : Admissible c₀ := hc_snoc.of_snoc
    have hB₀_j : AllValsLt c₀ j.val := hc_snoc.allValsLt_of_snoc
    dsimp only [insert]
    by_cases hlt : j.val < i.val
    · simp only [hlt]
      exact .cons hc_snoc hlt
    · simp only [hlt]
      have hi_lt_k : i.val < k + 2 := by
        have := j.is_lt
        omega
      let i' : Fin (k + 2) := Fin.mk i.val hi_lt_k
      have hi'_le_j : i'.val ≤ j.val := by
        simp [i']
        omega
      have ih_adm : Admissible (insert c₀ i') := ih hc₀ i'
      have ih_le : AllValsLe (insert c₀ i') j.val :=
        insert_allValsLe hc₀ hB₀_j i' hi'_le_j
      have hj_lt_succ : j.val < (Fin.succ j).val := by
        simp [Fin.val_succ]
      exact ih_adm.snoc_of_le_lt ih_le hj_lt_succ

/-- Normalize a face chain to strictly increasing order via iterated insertion sort. -/
def normalize {n : ℕ} : {m : ℕ} → DeltaChain n m → DeltaChain n m
  | _, .nil => DeltaChain.nil
  | _, .snoc c i => (normalize c).insert i

/-- Normalization preserves evaluation. -/
theorem normalize_eval {n m : ℕ} (c : DeltaChain n m) :
    (normalize c).eval = c.eval := by
  induction c with
  | nil => rfl
  | snoc c₀ j ih =>
    simp [normalize, insert_eval, ih]

/-- Normalization produces an admissible chain. -/
theorem normalize_admissible {n m : ℕ} (c : DeltaChain n m) :
    Admissible (normalize c) := by
  induction c with
  | nil =>
    simp only [normalize]
    exact .nil
  | snoc c₀ j ih =>
    simp only [normalize]
    exact insert_admissible ih _

/-- Appending a strictly larger element preserves `Pairwise (<)`. -/
private theorem pairwise_append_singleton {l : List ℕ} {a : ℕ}
    (hl : l.Pairwise (· < ·)) (ha : ∀ x ∈ l, x < a) :
    (l ++ [a]).Pairwise (· < ·) := by
  induction l with
  | nil =>
    simp only [List.nil_append]
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons b l' ih =>
    have hb_lt_a : b < a := ha b (List.mem_cons.mpr (Or.inl rfl))
    have hl_pair : l'.Pairwise (· < ·) :=
      (List.pairwise_cons.mp hl).2
    have hb_l' : ∀ y ∈ l', b < y :=
      (List.pairwise_cons.mp hl).1
    have ha' : ∀ x ∈ l', x < a := by
      intro x hx
      exact ha x (List.mem_cons.mpr (Or.inr hx))
    have ih' : (l' ++ [a]).Pairwise (· < ·) := ih hl_pair ha'
    have h_forall : ∀ y ∈ l' ++ [a], b < y := by
      intro y hy
      rcases List.mem_append.mp hy with hy' | hy'
      · exact hb_l' y hy'
      · rw [List.mem_singleton.mp hy']
        exact hb_lt_a
    exact (List.pairwise_cons.mpr ⟨h_forall, ih'⟩)

/-- Admissible chains have strictly increasing `toNatList` (pairwise `<`). -/
theorem Admissible.toNatList_pairwise_lt {n : ℕ} {m : ℕ} {c : DeltaChain n m}
    (h : Admissible c) : c.toNatList.Pairwise (· < ·) := by
  induction h with
  | nil =>
    simp only [toNatList]
    exact List.Pairwise.nil
  | singleton =>
    simp only [toNatList]
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | @cons k c₂ j i hAdm hlt ih =>
    simp only [toNatList]
    have h_all : AllValsLt c₂ j.val := allValsLt_of_snoc hAdm
    have h_forall_c₂ : ∀ y ∈ c₂.toNatList, y < j.val :=
      AllValsLt_iff_forall_mem_lt.mp h_all
    have h_forall : ∀ y ∈ (c₂.toNatList ++ [j.val]), y < i.val := by
      intro y hy
      rcases List.mem_append.mp hy with hy1 | hy1
      · have hy1_lt_j : y < j.val := h_forall_c₂ y hy1
        exact Nat.lt_trans hy1_lt_j hlt
      · rw [List.mem_singleton.mp hy1]
        exact hlt
    exact pairwise_append_singleton ih h_forall

/--
Admissible chains: their stored indices are exactly the missing values of
the evaluated order embedding.
-/
theorem Admissible.mem_toNatList_iff_not_mem_range_evalOrderHom
    {n m : ℕ} {c : DeltaChain n m} (hc : Admissible c) (j : Fin (m + 1)) :
    j.val ∈ c.toNatList ↔ j ∉ Set.range (evalOrderHom c) := by
  induction hc with
  | nil =>
    constructor
    · intro h
      simp [toNatList] at h
    · intro h_not
      have h_mem : j ∈ Set.range (evalOrderHom (DeltaChain.nil (n := n))) :=
        ⟨j, by simp [evalOrderHom_nil]⟩
      exact absurd h_mem h_not
  | @singleton i =>
    have h_nil_range : ∀ (k : ℕ) (x : Fin (k + 1)),
        x ∈ Set.range (evalOrderHom (DeltaChain.nil (n := k))) := by
      intro k x
      exact ⟨x, by simp [evalOrderHom_nil]⟩
    constructor
    · intro h_mem
      have h_eq_val : j.val = i.val := by
        have : j.val ∈ [i.val] := by
          simpa [toNatList] using h_mem
        exact List.mem_singleton.mp this
      have h_eq : j = i := Fin.ext h_eq_val
      rw [h_eq]
      exact not_mem_range_evalOrderHom_snoc (DeltaChain.nil (n := n)) i
    · intro h_not
      rcases lt_trichotomy j i with h_lt | rfl | h_gt
      · exfalso
        apply h_not
        let hNe := Fin.ne_last_of_lt (Fin.lt_of_lt_of_le h_lt i.le_last)
        have h_cast : (j.castPred hNe) ∈
            Set.range (evalOrderHom (DeltaChain.nil (n := n))) :=
          h_nil_range _ _
        rw [← mem_range_evalOrderHom_snoc_of_lt _ i j h_lt] at h_cast
        exact h_cast
      · simp [toNatList]
      · exfalso
        apply h_not
        let hNe := Fin.ne_zero_of_lt h_gt
        have h_pred : (j.pred hNe) ∈
            Set.range (evalOrderHom (DeltaChain.nil (n := n))) :=
          h_nil_range _ _
        rw [← mem_range_evalOrderHom_snoc_of_gt _ i j h_gt] at h_pred
        exact h_pred
  | @cons m c jPrev i h_adm h_lt_ij ih =>
    have h_all : AllValsLt (c.snoc jPrev) i.val :=
      Admissible.allValsLt_of_snoc (Admissible.cons h_adm h_lt_ij)
    have h_forall : ∀ x ∈ (c.snoc jPrev).toNatList, x < i.val :=
      AllValsLt_iff_forall_mem_lt.mp h_all
    constructor
    · intro h_mem_list
      rw [toNatList_snoc] at h_mem_list
      rcases List.mem_append.mp h_mem_list with h_old | h_eq
      · have h_lt : j < i := by
          have : j.val < i.val := h_forall _ h_old
          rwa [Fin.lt_def]
        let hNe := Fin.ne_last_of_lt (Fin.lt_of_lt_of_le h_lt i.le_last)
        have h_cast_val : (j.castPred hNe).val ∈ (c.snoc jPrev).toNatList := by
          have : (j.castPred hNe : ℕ) = j.val := Fin.coe_castPred _ _
          rw [this]
          exact h_old
        have h_cast_not : (j.castPred hNe) ∉
            Set.range (evalOrderHom (c.snoc jPrev)) := (ih _).mp h_cast_val
        intro h_in
        rw [mem_range_evalOrderHom_snoc_of_lt _ i j h_lt] at h_in
        exact h_cast_not h_in
      · have h_eq_val : j.val = i.val := List.mem_singleton.mp h_eq
        have h_eq_fin : j = i := Fin.ext h_eq_val
        rw [h_eq_fin]
        exact not_mem_range_evalOrderHom_snoc _ i
    · intro h_not_range
      rw [toNatList_snoc]
      rcases lt_trichotomy j i with h_lt | rfl | h_gt
      · let hNe := Fin.ne_last_of_lt (Fin.lt_of_lt_of_le h_lt i.le_last)
        have h_cast_not : (j.castPred hNe) ∉
            Set.range (evalOrderHom (c.snoc jPrev)) := by
          intro h_in
          apply h_not_range
          rw [mem_range_evalOrderHom_snoc_of_lt _ i j h_lt]
          exact h_in
        have h_cast_mem : (j.castPred hNe).val ∈ (c.snoc jPrev).toNatList :=
          (ih _).mpr h_cast_not
        have : (j.castPred hNe : ℕ) = j.val := Fin.coe_castPred _ _
        rw [this] at h_cast_mem
        exact List.mem_append.mpr (Or.inl h_cast_mem)
      · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · exfalso
        let hNeZero := Fin.ne_zero_of_lt h_gt
        have h_not_mem : (j.pred hNeZero).val ∉ (c.snoc jPrev).toNatList := by
          intro h_mem
          have h_lt_mem : (j.pred hNeZero).val < i.val := h_forall _ h_mem
          have h_pred_val : (j.pred hNeZero : ℕ) = j.val - 1 := by
            simp [Fin.val_pred]
          have h_i_lt_j : i.val < j.val := by
            rwa [← Fin.lt_def]
          omega
        have h_pred_range : (j.pred hNeZero) ∈
            Set.range (evalOrderHom (c.snoc jPrev)) := by
          have h_iff : (j.pred hNeZero) ∉ Set.range (evalOrderHom (c.snoc jPrev)) ↔
              (j.pred hNeZero).val ∈ (c.snoc jPrev).toNatList := (ih _).symm
          by_contra h_contra
          exact h_not_mem (h_iff.mp h_contra)
        have h_j_range : j ∈ Set.range (evalOrderHom ((c.snoc jPrev).snoc i)) := by
          rw [mem_range_evalOrderHom_snoc_of_gt (c.snoc jPrev) i j h_gt]
          exact h_pred_range
        exact h_not_range h_j_range

/-- Every `P_δ` morphism is represented by an admissible (strictly increasing) chain. -/
theorem exists_admissible_chain_of_P_delta {n m : ℕ}
    (f : mk n ⟶ mk m) (hf : P_δ f) :
    ∃ c : DeltaChain n m, Admissible c ∧ c.eval = f := by
  obtain ⟨c, hc⟩ := exists_chain_mk_mk_of_P_delta f hf
  refine ⟨normalize c, normalize_admissible c, ?_⟩
  rw [normalize_eval, hc]

/--
Fixed-endpoint uniqueness of admissible chains from equality of evaluated
order homomorphisms. This is the primary uniqueness theorem; the range/list
argument occurs only here and is reused by the weaker corollaries below.
-/
theorem Admissible.eq_of_evalOrderHom_eq {n m : ℕ} {c d : DeltaChain n m}
    (hc : Admissible c) (hd : Admissible d)
    (h : evalOrderHom c = evalOrderHom d) : c = d := by
  have h_range : Set.range (evalOrderHom c) = Set.range (evalOrderHom d) := by
    rw [h]
  have h_mem_iff : ∀ a : ℕ, a ∈ c.toNatList ↔ a ∈ d.toNatList := by
    intro a
    by_cases ha : a < m + 1
    · let j : Fin (m + 1) := ⟨a, ha⟩
      have hj : j.val = a := rfl
      have hc_iff : a ∈ c.toNatList ↔ j ∉ Set.range (evalOrderHom c) := by
        rw [← hj]
        exact Admissible.mem_toNatList_iff_not_mem_range_evalOrderHom hc j
      have hd_iff : a ∈ d.toNatList ↔ j ∉ Set.range (evalOrderHom d) := by
        rw [← hj]
        exact Admissible.mem_toNatList_iff_not_mem_range_evalOrderHom hd j
      have h_not_range : j ∉ Set.range (evalOrderHom c) ↔ j ∉ Set.range (evalOrderHom d) := by
        rw [h_range]
      exact hc_iff.trans (h_not_range.trans hd_iff.symm)
    · have hc_not : a ∉ c.toNatList := by
        intro hmem
        have := mem_toNatList_lt hmem
        omega
      have hd_not : a ∉ d.toNatList := by
        intro hmem
        have := mem_toNatList_lt hmem
        omega
      exact ⟨fun hmem => absurd hmem hc_not, fun hmem => absurd hmem hd_not⟩
  have hc_pair : c.toNatList.Pairwise (· < ·) := hc.toNatList_pairwise_lt
  have hd_pair : d.toNatList.Pairwise (· < ·) := hd.toNatList_pairwise_lt
  have h_list_eq : c.toNatList = d.toNatList :=
    List.Pairwise.eq_of_mem_iff hc_pair hd_pair h_mem_iff
  exact eq_of_toNatList_eq h_list_eq

/--
Fixed-endpoint uniqueness from equality of the images under
`toSimplexCategory.map`. Thin corollary of `eq_of_evalOrderHom_eq` usable
for faithfulness.
-/
theorem Admissible.eq_of_toSimplexCategory_map_eq {n m : ℕ} {c d : DeltaChain n m}
    (hc : Admissible c) (hd : Admissible d)
    (h : toSimplexCategory.map c.eval = toSimplexCategory.map d.eval) : c = d := by
  have h_ord : evalOrderHom c = evalOrderHom d := by
    unfold evalOrderHom
    rw [h]
  exact Admissible.eq_of_evalOrderHom_eq hc hd h_ord

/-- Fixed-endpoint uniqueness of admissible chains from equality of evaluations. -/
theorem Admissible.eq_of_eval_eq {n m : ℕ} {c d : DeltaChain n m}
    (hc : Admissible c) (hd : Admissible d) (h : c.eval = d.eval) : c = d := by
  have h_map : toSimplexCategory.map c.eval = toSimplexCategory.map d.eval := by
    rw [h]
  exact Admissible.eq_of_toSimplexCategory_map_eq hc hd h_map

end DeltaChain

end SimplexCategoryGenRel
