/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Combinatorics.Hall.Basic

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted

/-!
# Edge coloring landmarks

Records Vizing and König edge-coloring theorems.
-/

/-- **Proper edge coloring.** Let $G$ be a simple graph on $V$. An edge labeling $C$ of $G$ with
colors in $K$ is a proper edge coloring when any two distinct edges of $G$ that share a vertex
receive different colors: whenever a vertex $v$ is adjacent to $w_1$ and to $w_2$ with
$w_1 \ne w_2$, the edges $v w_1$ and $v w_2$ have different colors under $C$. -/
def IsProperEdgeColoring {V K : Type*} {G : _root_.SimpleGraph V}
    (C : G.EdgeLabeling K) : Prop :=
  ∀ {v w₁ w₂ : V} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂), w₁ ≠ w₂ →
    C ⟨Sym2.mk v w₁, G.mem_edgeSet.mpr h₁⟩ ≠ C ⟨Sym2.mk v w₂, G.mem_edgeSet.mpr h₂⟩

/-- König's line coloring, regular multigraph case: a `d`-regular bipartite
multigraph (given by endpoint projections) is `d`-edge-colorable. The proof
extracts a perfect matching by Hall's theorem and inducts. Shared API also
used by the multigraph Galvin development. -/
theorem multigraph_regular_color.{u, v} (d : ℕ) (A B : Type u) (E : Type v)
    [Finite A] [DecidableEq A] [Finite B] [DecidableEq B]
    [Fintype E]
    (l : E → A) (r : E → B)
    (hL : ∀ a, (Finset.univ.filter (fun e => l e = a)).card = d)
    (hR : ∀ b, (Finset.univ.filter (fun e => r e = b)).card = d) :
    ∃ C : E → Fin d,
      (∀ e₁ e₂, l e₁ = l e₂ → C e₁ = C e₂ → e₁ = e₂) ∧
      (∀ e₁ e₂, r e₁ = r e₂ → C e₁ = C e₂ → e₁ = e₂) := by
  classical
  induction d generalizing A B E l r with
  | zero =>
    have hEmpty : IsEmpty E := by
      constructor
      intro e
      have hmem : e ∈ Finset.univ.filter (fun e' : E => l e' = l e) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ e, rfl⟩
      have hempty : Finset.univ.filter (fun e' : E => l e' = l e) = ∅ :=
        Finset.card_eq_zero.mp (hL (l e))
      rw [hempty] at hmem
      exact Finset.notMem_empty e hmem
    exact ⟨fun e => (hEmpty.false e).elim, fun e₁ => (hEmpty.false e₁).elim,
      fun e₁ => (hEmpty.false e₁).elim⟩
  | succ d ih =>
    classical
    have := Fintype.ofFinite A
    have := Fintype.ofFinite B
    -- Hall condition
    have hall : ∀ S : Finset A, S.card ≤
        (S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r)).card := by
      intro S
      have hES_eq : (Finset.univ.filter (fun e : E => l e ∈ S)).card = S.card * (d + 1) := by
        have hmaps : Set.MapsTo l (↑(Finset.univ.filter (fun e : E => l e ∈ S)) : Set E)
            (↑S : Set A) := by
          intro e he
          have heF : e ∈ Finset.univ.filter (fun e : E => l e ∈ S) := he
          exact (Finset.mem_filter.mp heF).2
        have hfib := Finset.card_eq_sum_card_fiberwise (f := l)
          (s := Finset.univ.filter (fun e : E => l e ∈ S)) (t := S) hmaps
        have hterm : ∀ a ∈ S, ({e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | l e = a}).card = d +
            1 := by
          intro a ha
          have hset_eq : {e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | l e = a} =
              Finset.univ.filter (fun e : E => l e = a) := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h; exact h.2
            · intro h; exact ⟨h ▸ ha, h⟩
          rw [hset_eq, hL]
        calc (Finset.univ.filter (fun e : E => l e ∈ S)).card
            = ∑ a ∈ S, ({e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | l e = a}).card := hfib
          _ = ∑ _ ∈ S, (d + 1) := Finset.sum_congr rfl hterm
          _ = S.card * (d + 1) := by simp [Finset.sum_const, smul_eq_mul]
      have hES_le : (Finset.univ.filter (fun e : E => l e ∈ S)).card ≤
          (S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r)).card *
              (d + 1) := by
        have hmaps2 : Set.MapsTo r (↑(Finset.univ.filter (fun e : E => l e ∈ S)) : Set E)
            (↑(S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r)) : Set
                B) := by
          intro e he
          have heF : e ∈ Finset.univ.filter (fun e : E => l e ∈ S) := he
          have hmemS : l e ∈ S := (Finset.mem_filter.mp heF).2
          have hmem_im : r e ∈ (Finset.univ.filter (fun e' : E => l e' = l e)).image r :=
            Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, rfl⟩, rfl⟩
          have hmem_bi : r e ∈ S.biUnion (fun a =>
              (Finset.univ.filter (fun e' : E => l e' = a)).image r) :=
            Finset.mem_biUnion.mpr ⟨l e, hmemS, hmem_im⟩
          exact hmem_bi
        have hfib2 := Finset.card_eq_sum_card_fiberwise (f := r)
          (s := Finset.univ.filter (fun e : E => l e ∈ S))
          (t := S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r)) hmaps2
        have hterm2 : ∀ b ∈ S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image
            r),
            ({e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | r e = b}).card ≤ d + 1 := by
          intro b _
          have hsub : {e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | r e = b} ⊆
              Finset.univ.filter (fun e : E => r e = b) := by
            intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
            exact he.2
          calc ({e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | r e = b}).card ≤
                (Finset.univ.filter (fun e : E => r e = b)).card := Finset.card_le_card hsub
            _ = d + 1 := hR b
        calc (Finset.univ.filter (fun e : E => l e ∈ S)).card
            = ∑ b ∈ S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r),
                ({e ∈ Finset.univ.filter (fun e : E => l e ∈ S) | r e = b}).card := hfib2
          _ ≤ ∑ _ ∈ S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r),
              (d + 1) :=
              Finset.sum_le_sum hterm2
          _ = (S.biUnion (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r)).card *
              (d + 1) := by
              simp [Finset.sum_const, smul_eq_mul]
      exact Nat.le_of_mul_le_mul_right (hES_eq ▸ hES_le) (Nat.succ_pos d)
    -- matching
    obtain ⟨f, hf_inj, hf_ex⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (fun a => (Finset.univ.filter (fun e : E => l e = a)).image r)).mp hall
    have hex : ∀ a, ∃ e : E, l e = a ∧ r e = f a := by
      intro a
      have hmem := hf_ex a
      rw [Finset.mem_image] at hmem
      obtain ⟨e, he_mem, he_eq⟩ := hmem
      exact ⟨e, (Finset.mem_filter.mp he_mem).2, he_eq⟩
    choose pick hpickL hpickR using hex
    have hpick_inj : Function.Injective pick := by
      intro a₁ a₂ h
      have h1 := hpickL a₁
      have h2 := hpickL a₂
      rw [h] at h1
      exact h1.symm.trans h2
    -- card equality and bijectivity
    have hcard_eq : Fintype.card A = Fintype.card B := by
      have hE_A : Fintype.card E = Fintype.card A * (d + 1) := by
        have hmaps : Set.MapsTo l (↑(Finset.univ : Finset E) : Set E)
            (↑(Finset.univ : Finset A) : Set A) := by
          intro e _; exact Finset.mem_univ (l e)
        have hfib := Finset.card_eq_sum_card_fiberwise (f := l) (s := Finset.univ)
            (t := Finset.univ) hmaps
        simp only [Finset.card_univ] at hfib
        have hterm : ∀ a ∈ (Finset.univ : Finset A), ({e ∈ (Finset.univ : Finset E) | l e = a}).card
            = d + 1 := by
          intro a _
          have hset_eq : {e ∈ (Finset.univ : Finset E) | l e = a} =
              Finset.univ.filter (fun e : E => l e = a) := by ext e; simp
          rw [hset_eq, hL]
        calc Fintype.card E = ∑ a ∈ (Finset.univ : Finset A),
            ({e ∈ (Finset.univ : Finset E) | l e = a}).card := hfib
          _ = ∑ _ ∈ (Finset.univ : Finset A), (d + 1) := Finset.sum_congr rfl hterm
          _ = Fintype.card A * (d + 1) := by simp [Finset.sum_const, smul_eq_mul]
      have hE_B : Fintype.card E = Fintype.card B * (d + 1) := by
        have hmaps : Set.MapsTo r (↑(Finset.univ : Finset E) : Set E)
            (↑(Finset.univ : Finset B) : Set B) := by
          intro e _; exact Finset.mem_univ (r e)
        have hfib := Finset.card_eq_sum_card_fiberwise (f := r) (s := Finset.univ)
            (t := Finset.univ) hmaps
        simp only [Finset.card_univ] at hfib
        have hterm : ∀ b ∈ (Finset.univ : Finset B), ({e ∈ (Finset.univ : Finset E) | r e = b}).card
            = d + 1 := by
          intro b _
          have hset_eq : {e ∈ (Finset.univ : Finset E) | r e = b} =
              Finset.univ.filter (fun e : E => r e = b) := by ext e; simp
          rw [hset_eq, hR]
        calc Fintype.card E = ∑ b ∈ (Finset.univ : Finset B),
            ({e ∈ (Finset.univ : Finset E) | r e = b}).card := hfib
          _ = ∑ _ ∈ (Finset.univ : Finset B), (d + 1) := Finset.sum_congr rfl hterm
          _ = Fintype.card B * (d + 1) := by simp [Finset.sum_const, smul_eq_mul]
      have h : Fintype.card A * (d + 1) = Fintype.card B * (d + 1) := hE_A.symm.trans hE_B
      exact Nat.mul_right_cancel (Nat.succ_pos d) h
    have hf_bij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard_eq⟩
    let fEquiv := Equiv.ofBijective f hf_bij
    have hfEq : ∀ a, fEquiv a = f a := fun a => rfl
    -- remainder type
    let E' := {e : E // e ∉ Set.range pick}
    let l' : E' → A := fun e' => l e'.val
    let r' : E' → B := fun e' => r e'.val
    have hL' : ∀ a, (Finset.univ.filter (fun e' : E' => l' e' = a)).card = d := by
      intro a
      have hmem : pick a ∈ Finset.univ.filter (fun e : E => l e = a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpickL a⟩
      have herase : ((Finset.univ.filter (fun e : E => l e = a)).erase (pick a)).card = d := by
        rw [Finset.card_erase_of_mem hmem, hL a, Nat.add_sub_cancel]
      have hbij := Finset.card_bij (s := Finset.univ.filter (fun e' : E' => l' e' = a))
        (t := (Finset.univ.filter (fun e : E => l e = a)).erase (pick a))
        (i := fun (e' : E') _ => e'.val)
        (by
          intro e' he'
          have hla : l e'.val = a := (Finset.mem_filter.mp he').2
          have hne : e'.val ≠ pick a := fun hcon => e'.prop ⟨a, hcon.symm⟩
          rw [Finset.mem_erase]
          exact ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩⟩)
        (by intro e₁ _ e₂ _ h; exact Subtype.ext h)
        (by
          intro e he
          rw [Finset.mem_erase] at he
          obtain ⟨hne, hmemF⟩ := he
          have hla : l e = a := (Finset.mem_filter.mp hmemF).2
          have hnr : e ∉ Set.range pick := by
            rintro ⟨a', ha'⟩
            have haa2 : a' = a := by rw [← hpickL a', ha', hla]
            subst haa2
            exact hne ha'.symm
          exact ⟨⟨e, hnr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩, rfl⟩)
      calc (Finset.univ.filter (fun e' : E' => l' e' = a)).card
          = ((Finset.univ.filter (fun e : E => l e = a)).erase (pick a)).card := hbij
        _ = d := herase
    have hR' : ∀ b, (Finset.univ.filter (fun e' : E' => r' e' = b)).card = d := by
      intro b
      let a₀ := fEquiv.symm b
      have hf0 : f a₀ = b := by simp [a₀, ← hfEq, Equiv.apply_symm_apply fEquiv b]
      have hmem : pick a₀ ∈ Finset.univ.filter (fun e : E => r e = b) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hpickR a₀).trans hf0⟩
      have herase : ((Finset.univ.filter (fun e : E => r e = b)).erase (pick a₀)).card = d := by
        rw [Finset.card_erase_of_mem hmem, hR b, Nat.add_sub_cancel]
      have hbij := Finset.card_bij (s := Finset.univ.filter (fun e' : E' => r' e' = b))
        (t := (Finset.univ.filter (fun e : E => r e = b)).erase (pick a₀))
        (i := fun (e' : E') _ => e'.val)
        (by
          intro e' he'
          have hrb : r e'.val = b := (Finset.mem_filter.mp he').2
          have hne : e'.val ≠ pick a₀ := fun hcon => e'.prop ⟨a₀, hcon.symm⟩
          rw [Finset.mem_erase]
          exact ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrb⟩⟩)
        (by intro e₁ _ e₂ _ h; exact Subtype.ext h)
        (by
          intro e he
          rw [Finset.mem_erase] at he
          obtain ⟨hne, hmemF⟩ := he
          have hrb : r e = b := (Finset.mem_filter.mp hmemF).2
          have hnr : e ∉ Set.range pick := by
            rintro ⟨a', ha'⟩
            have hfa : f a' = b := by rw [← hpickR a', ha', hrb]
            have haa : a' = a₀ := hf_inj (hfa.trans hf0.symm)
            subst haa
            exact hne ha'.symm
          exact ⟨⟨e, hnr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrb⟩, rfl⟩)
      calc (Finset.univ.filter (fun e' : E' => r' e' = b)).card
          = ((Finset.univ.filter (fun e : E => r e = b)).erase (pick a₀)).card := hbij
        _ = d := herase
    obtain ⟨C', hC'L, hC'R⟩ := ih A B E' l' r' hL' hR'
    -- assemble colors
    have hdec : ∀ e : E, Decidable (e ∈ Set.range pick) := fun e => Classical.dec _
    let C : E → Fin (d + 1) := fun e =>
      if h : e ∈ Set.range pick then 0 else (C' ⟨e, h⟩).succ
    refine ⟨C, ?_, ?_⟩
    · intro e₁ e₂ hle hce
      simp only [C] at hce
      by_cases h1 : e₁ ∈ Set.range pick <;> by_cases h2 : e₂ ∈ Set.range pick
      · obtain ⟨a₁, ha₁⟩ := h1
        obtain ⟨a₂, ha₂⟩ := h2
        have hll : l (pick a₁) = l (pick a₂) := by rw [ha₁, ha₂, hle]
        rw [hpickL a₁, hpickL a₂] at hll
        rw [hll] at ha₁
        exact ha₁.symm.trans ha₂
      · rw [dite_eq_left h1, dite_eq_right h2] at hce
        exact (Fin.succ_ne_zero _ hce.symm).elim
      · rw [dite_eq_right h1, dite_eq_left h2] at hce
        exact (Fin.succ_ne_zero _ hce).elim
      · rw [dite_eq_right h1, dite_eq_right h2] at hce
        have hcs : C' ⟨e₁, h1⟩ = C' ⟨e₂, h2⟩ := Fin.succ_inj.mp hce
        have hl' : l' ⟨e₁, h1⟩ = l' ⟨e₂, h2⟩ := hle
        have hsub := hC'L _ _ hl' hcs
        exact congrArg Subtype.val hsub
    · intro e₁ e₂ hre hce
      simp only [C] at hce
      by_cases h1 : e₁ ∈ Set.range pick <;> by_cases h2 : e₂ ∈ Set.range pick
      · obtain ⟨a₁, ha₁⟩ := h1
        obtain ⟨a₂, ha₂⟩ := h2
        have hrr : r (pick a₁) = r (pick a₂) := by rw [ha₁, ha₂, hre]
        rw [hpickR a₁, hpickR a₂] at hrr
        have haa : a₁ = a₂ := hf_inj hrr
        rw [haa] at ha₁
        exact ha₁.symm.trans ha₂
      · rw [dite_eq_left h1, dite_eq_right h2] at hce
        exact (Fin.succ_ne_zero _ hce.symm).elim
      · rw [dite_eq_right h1, dite_eq_left h2] at hce
        exact (Fin.succ_ne_zero _ hce).elim
      · rw [dite_eq_right h1, dite_eq_right h2] at hce
        have hcs : C' ⟨e₁, h1⟩ = C' ⟨e₂, h2⟩ := Fin.succ_inj.mp hce
        have hr' : r' ⟨e₁, h1⟩ = r' ⟨e₂, h2⟩ := hre
        have hsub := hC'R _ _ hr' hcs
        exact congrArg Subtype.val hsub


/-- König's line coloring, bounded-degree multigraph case: a bipartite
multigraph of maximum degree at most `d` is `d`-edge-colorable. The proof
pads both sides with dummy edges to reach the regular case. Shared API also
used by the multigraph Galvin development. -/
theorem multigraph_bounded_color.{u, v} (d : ℕ) (A B : Type u) (E : Type v)
    [Finite A] [DecidableEq A] [Finite B] [DecidableEq B]
    [Fintype E]
    (l : E → A) (r : E → B)
    (hL : ∀ a, (Finset.univ.filter (fun e => l e = a)).card ≤ d)
    (hR : ∀ b, (Finset.univ.filter (fun e => r e = b)).card ≤ d) :
    ∃ C : E → Fin d,
      (∀ e₁ e₂, l e₁ = l e₂ → C e₁ = C e₂ → e₁ = e₂) ∧
      (∀ e₁ e₂, r e₁ = r e₂ → C e₁ = C e₂ → e₁ = e₂) := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  let lEmb : E → A ⊕ B := Sum.inl ∘ l
  let rEmb : E → B ⊕ A := Sum.inl ∘ r
  let degL : A ⊕ B → ℕ := fun x => (Finset.univ.filter (fun e : E => lEmb e = x)).card
  let degR : B ⊕ A → ℕ := fun y => (Finset.univ.filter (fun e : E => rEmb e = y)).card
  have hdegL_le : ∀ x, degL x ≤ d := by
    intro x
    cases x with
    | inl a =>
      change (Finset.univ.filter (fun e : E => lEmb e = Sum.inl a)).card ≤ d
      have heq : (Finset.univ.filter (fun e : E => lEmb e = Sum.inl a)) =
          Finset.univ.filter (fun e : E => l e = a) := by
        ext e
        simp [lEmb]
      rw [heq]
      exact hL a
    | inr b =>
      change (Finset.univ.filter (fun e : E => lEmb e = Sum.inr b)).card ≤ d
      have heq : (Finset.univ.filter (fun e : E => lEmb e = Sum.inr b)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e _ hcon
        simp [lEmb] at hcon
      rw [heq]
      simp
  have hdegR_le : ∀ y, degR y ≤ d := by
    intro y
    cases y with
    | inl b =>
      change (Finset.univ.filter (fun e : E => rEmb e = Sum.inl b)).card ≤ d
      have heq : (Finset.univ.filter (fun e : E => rEmb e = Sum.inl b)) =
          Finset.univ.filter (fun e : E => r e = b) := by
        ext e
        simp [rEmb]
      rw [heq]
      exact hR b
    | inr a =>
      change (Finset.univ.filter (fun e : E => rEmb e = Sum.inr a)).card ≤ d
      have heq : (Finset.univ.filter (fun e : E => rEmb e = Sum.inr a)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e _ hcon
        simp [rEmb] at hcon
      rw [heq]
      simp
  have hsumL : ∑ x : A ⊕ B, degL x = Fintype.card E := by
    have hmaps : Set.MapsTo lEmb (↑(Finset.univ : Finset E) : Set E)
        (↑(Finset.univ : Finset (A ⊕ B)) : Set (A ⊕ B)) := by
      intro e _
      exact Finset.mem_univ _
    have hfib := Finset.card_eq_sum_card_fiberwise (f := lEmb)
      (s := Finset.univ) (t := Finset.univ) hmaps
    simp only [Finset.card_univ] at hfib
    have hterm : ∀ x ∈ (Finset.univ : Finset (A ⊕ B)),
        ({e ∈ (Finset.univ : Finset E) | lEmb e = x}).card = degL x := by
      intro x _
      have hset_eq : {e ∈ (Finset.univ : Finset E) | lEmb e = x} =
          Finset.univ.filter (fun e : E => lEmb e = x) := by ext e; simp
      exact congrArg Finset.card hset_eq
    calc ∑ x : A ⊕ B, degL x
        = ∑ x ∈ (Finset.univ : Finset (A ⊕ B)),
          ({e ∈ (Finset.univ : Finset E) | lEmb e = x}).card := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (hterm x hx).symm
      _ = Fintype.card E := hfib.symm
  have hsumR : ∑ y : B ⊕ A, degR y = Fintype.card E := by
    have hmaps : Set.MapsTo rEmb (↑(Finset.univ : Finset E) : Set E)
        (↑(Finset.univ : Finset (B ⊕ A)) : Set (B ⊕ A)) := by
      intro e _
      exact Finset.mem_univ _
    have hfib := Finset.card_eq_sum_card_fiberwise (f := rEmb)
      (s := Finset.univ) (t := Finset.univ) hmaps
    simp only [Finset.card_univ] at hfib
    have hterm : ∀ y ∈ (Finset.univ : Finset (B ⊕ A)),
        ({e ∈ (Finset.univ : Finset E) | rEmb e = y}).card = degR y := by
      intro y _
      have hset_eq : {e ∈ (Finset.univ : Finset E) | rEmb e = y} =
          Finset.univ.filter (fun e : E => rEmb e = y) := by ext e; simp
      exact congrArg Finset.card hset_eq
    calc ∑ y : B ⊕ A, degR y
        = ∑ y ∈ (Finset.univ : Finset (B ⊕ A)),
          ({e ∈ (Finset.univ : Finset E) | rEmb e = y}).card := by
            apply Finset.sum_congr rfl
            intro y hy
            exact (hterm y hy).symm
      _ = Fintype.card E := hfib.symm
  let Lstub := Sigma (fun x : A ⊕ B => Fin (d - degL x))
  let Rstub := Sigma (fun y : B ⊕ A => Fin (d - degR y))
  have hcard_eq : Fintype.card Lstub = Fintype.card Rstub := by
    have hLcard : Fintype.card Lstub = Fintype.card (A ⊕ B) * d - Fintype.card E := by
      have h1 : Fintype.card Lstub = ∑ x ∈ (Finset.univ : Finset (A ⊕ B)), (d - degL x) := by
        have hsig := Fintype.card_sigma (ι := A ⊕ B) (α := fun x => Fin (d - degL x))
        simp only [Fintype.card_fin] at hsig
        have hrr : (∑ x : A ⊕ B, (d - degL x)) =
            ∑ x ∈ (Finset.univ : Finset (A ⊕ B)), (d - degL x) := rfl
        rw [← hrr]
        exact hsig
      have h2 := Finset.sum_tsub_distrib (Finset.univ : Finset (A ⊕ B))
        (f := fun _ => d) (g := degL) (fun x _ => hdegL_le x)
      have hsum_d : ∑ x ∈ (Finset.univ : Finset (A ⊕ B)), d = Fintype.card (A ⊕ B) * d := by
        simp [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      have hsum_deg : ∑ x ∈ (Finset.univ : Finset (A ⊕ B)), degL x = Fintype.card E := hsumL
      rw [h1, h2, hsum_d, hsum_deg]
    have hRcard : Fintype.card Rstub = Fintype.card (B ⊕ A) * d - Fintype.card E := by
      have h1 : Fintype.card Rstub = ∑ y ∈ (Finset.univ : Finset (B ⊕ A)), (d - degR y) := by
        have hsig := Fintype.card_sigma (ι := B ⊕ A) (α := fun y => Fin (d - degR y))
        simp only [Fintype.card_fin] at hsig
        have hrr : (∑ y : B ⊕ A, (d - degR y)) =
            ∑ y ∈ (Finset.univ : Finset (B ⊕ A)), (d - degR y) := rfl
        rw [← hrr]
        exact hsig
      have h2 := Finset.sum_tsub_distrib (Finset.univ : Finset (B ⊕ A))
        (f := fun _ => d) (g := degR) (fun y _ => hdegR_le y)
      have hsum_d : ∑ y ∈ (Finset.univ : Finset (B ⊕ A)), d = Fintype.card (B ⊕ A) * d := by
        simp [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      have hsum_deg : ∑ y ∈ (Finset.univ : Finset (B ⊕ A)), degR y = Fintype.card E := hsumR
      rw [h1, h2, hsum_d, hsum_deg]
    have hAB : Fintype.card (A ⊕ B) = Fintype.card (B ⊕ A) := by
      rw [Fintype.card_sum, Fintype.card_sum, Nat.add_comm]
    rw [hLcard, hRcard, hAB]
  let equiv := Fintype.equivOfCardEq hcard_eq
  let E2 := E ⊕ Lstub
  let l2 : E2 → A ⊕ B := Sum.elim lEmb (fun s => s.1)
  let r2 : E2 → B ⊕ A := Sum.elim rEmb (fun s => (equiv s).1)
  have hregL : ∀ x : A ⊕ B, (Finset.univ.filter (fun e' : E2 => l2 e' = x)).card = d := by
    intro x
    have hconv : (Finset.univ.filter (fun e' : E2 => l2 e' = x)).card =
        Fintype.card {e' : E2 // l2 e' = x} := by
      have h := Fintype.card_ofFinset
        (s := Finset.univ.filter (fun e' : E2 => l2 e' = x))
        (p := {e' | l2 e' = x}) (by intro e'; simp)
      exact h.symm
    rw [hconv]
    have hequiv : {e' : E2 // l2 e' = x} ≃ {e : E // lEmb e = x} ⊕ {s : Lstub // s.1 = x} :=
      Equiv.subtypeSum
    have hleft : Fintype.card {e : E // lEmb e = x} = degL x := by
      have h := Fintype.card_ofFinset
        (s := Finset.univ.filter (fun e : E => lEmb e = x))
        (p := {e | lEmb e = x}) (by intro e; simp)
      change Fintype.card ↥{e | lEmb e = x} = degL x
      have hdeg : degL x = (Finset.univ.filter (fun e : E => lEmb e = x)).card := rfl
      rw [hdeg, ← h]
    have hright : Fintype.card {s : Lstub // s.1 = x} = d - degL x := by
      have he2 : {s : Lstub // s.1 = x} ≃ Fin (d - degL x) := Equiv.sigmaSubtype x
      rw [Fintype.card_congr he2, Fintype.card_fin]
    calc Fintype.card {e' : E2 // l2 e' = x}
        = Fintype.card ({e : E // lEmb e = x} ⊕ {s : Lstub // s.1 = x}) :=
          Fintype.card_congr hequiv
      _ = Fintype.card {e : E // lEmb e = x} + Fintype.card {s : Lstub // s.1 = x} :=
          Fintype.card_sum
      _ = degL x + (d - degL x) := by rw [hleft, hright]
      _ = d := Nat.add_sub_cancel' (hdegL_le x)
  have hregR : ∀ y : B ⊕ A, (Finset.univ.filter (fun e' : E2 => r2 e' = y)).card = d := by
    intro y
    have hconv : (Finset.univ.filter (fun e' : E2 => r2 e' = y)).card =
        Fintype.card {e' : E2 // r2 e' = y} := by
      have h := Fintype.card_ofFinset
        (s := Finset.univ.filter (fun e' : E2 => r2 e' = y))
        (p := {e' | r2 e' = y}) (by intro e'; simp)
      exact h.symm
    rw [hconv]
    have hequiv : {e' : E2 // r2 e' = y} ≃ {e : E // rEmb e = y} ⊕ {s : Lstub // (equiv s).1 = y} :=
      Equiv.subtypeSum
    have hleft : Fintype.card {e : E // rEmb e = y} = degR y := by
      have h := Fintype.card_ofFinset
        (s := Finset.univ.filter (fun e : E => rEmb e = y))
        (p := {e | rEmb e = y}) (by intro e; simp)
      change Fintype.card ↥{e | rEmb e = y} = degR y
      have hdeg : degR y = (Finset.univ.filter (fun e : E => rEmb e = y)).card := rfl
      rw [hdeg, ← h]
    have hright : Fintype.card {s : Lstub // (equiv s).1 = y} = d - degR y := by
      have he2 : {s : Lstub // (equiv s).1 = y} ≃ {t : Rstub // t.1 = y} :=
        equiv.subtypeEquiv (fun s => Iff.rfl)
      have he3 : {t : Rstub // t.1 = y} ≃ Fin (d - degR y) := Equiv.sigmaSubtype y
      rw [Fintype.card_congr he2, Fintype.card_congr he3, Fintype.card_fin]
    calc Fintype.card {e' : E2 // r2 e' = y}
        = Fintype.card ({e : E // rEmb e = y} ⊕ {s : Lstub // (equiv s).1 = y}) :=
          Fintype.card_congr hequiv
      _ = Fintype.card {e : E // rEmb e = y} + Fintype.card {s : Lstub // (equiv s).1 = y} :=
          Fintype.card_sum
      _ = degR y + (d - degR y) := by rw [hleft, hright]
      _ = d := Nat.add_sub_cancel' (hdegR_le y)
  obtain ⟨C2, hC2L, hC2R⟩ := multigraph_regular_color d (A ⊕ B) (B ⊕ A) E2 l2 r2 hregL hregR
  refine ⟨fun e => C2 (Sum.inl e), ?_, ?_⟩
  · intro e₁ e₂ hle hce
    have hll : l2 (Sum.inl e₁ : E2) = l2 (Sum.inl e₂ : E2) := by
      change lEmb e₁ = lEmb e₂
      simp [lEmb, hle]
    have hsub := hC2L _ _ hll hce
    exact Sum.inl_injective hsub
  · intro e₁ e₂ hre hce
    have hrr : r2 (Sum.inl e₁ : E2) = r2 (Sum.inl e₂ : E2) := by
      change rEmb e₁ = rEmb e₂
      simp [rEmb, hre]
    have hsub := hC2R _ _ hrr hce
    exact Sum.inl_injective hsub

/--
**König's line coloring theorem.** Every finite bipartite simple graph $G$ has a proper edge
coloring with $\Delta(G)$ colors, where $\Delta(G)$ is the maximum degree of $G$.

Since every proper edge coloring of $G$ needs at least $\Delta(G)$ colors, the edge chromatic
number of $G$ equals $\Delta(G)$.

Proves `Wanted` entry `konig_line_coloring`.

Source: D. Konig, Theorie der endlichen und unendlichen Graphen, Akademische Verlagsgesellschaft
(1936).
-/
theorem konig_line_coloring :
    ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.IsBipartite → ∃ C : G.EdgeLabeling (Fin G.maxDegree), IsProperEdgeColoring C := by
  intro V G _ _ hb
  obtain ⟨s, t, hst⟩ := SimpleGraph.IsBipartite.exists_isBipartiteWith hb
  classical
  have hor : ∀ e : ↥G.edgeSet, ∃ a b, a ∈ s ∧ b ∈ t ∧ Sym2.mk a b = e.val := by
    intro e
    obtain ⟨v, hv⟩ := e
    induction v using Sym2.ind with
    | _ a b =>
      have hadj : G.Adj a b := G.mem_edgeSet.mp hv
      rcases hst.mem_of_adj hadj with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨a, b, ha, hb, rfl⟩
      · exact ⟨b, a, hb, ha, Sym2.eq_swap⟩
  choose l r hls hrt hsym using hor
  have hadj_lr : ∀ e : ↥G.edgeSet, G.Adj (l e) (r e) := by
    intro e
    have hmem : Sym2.mk (l e) (r e) ∈ G.edgeSet := hsym e ▸ e.prop
    exact G.mem_edgeSet.mp hmem
  have hor_inj_pair : ∀ e₁ e₂ : ↥G.edgeSet, l e₁ = l e₂ → r e₁ = r e₂ → e₁ = e₂ := by
    intro e₁ e₂ hl hr
    apply Subtype.ext
    show e₁.val = e₂.val
    rw [← hsym e₁, ← hsym e₂, hl, hr]
  have hLb : ∀ a : V, (Finset.univ.filter (fun e : ↥G.edgeSet => l e = a)).card ≤ G.maxDegree := by
    intro a
    by_cases ha : a ∈ s
    · have hle : (Finset.univ.filter (fun e : ↥G.edgeSet => l e = a)).card ≤
          (G.neighborFinset a).card := by
        apply Finset.card_le_card_of_injOn (fun e => r e)
        · intro e he
          have heF : e ∈ Finset.univ.filter (fun e : ↥G.edgeSet => l e = a) := he
          have hla : l e = a := (Finset.mem_filter.mp heF).2
          have hadj : G.Adj a (r e) := hla ▸ hadj_lr e
          exact Finset.mem_coe.mpr ((SimpleGraph.mem_neighborFinset G a _).mpr hadj)
        · intro e₁ he₁ e₂ he₂ hrr
          have heF₁ : e₁ ∈ Finset.univ.filter (fun e : ↥G.edgeSet => l e = a) := he₁
          have heF₂ : e₂ ∈ Finset.univ.filter (fun e : ↥G.edgeSet => l e = a) := he₂
          have hl₁ : l e₁ = a := (Finset.mem_filter.mp heF₁).2
          have hl₂ : l e₂ = a := (Finset.mem_filter.mp heF₂).2
          have hl : l e₁ = l e₂ := hl₁.trans hl₂.symm
          exact hor_inj_pair e₁ e₂ hl hrr
      calc (Finset.univ.filter (fun e : ↥G.edgeSet => l e = a)).card
          ≤ (G.neighborFinset a).card := hle
        _ = G.degree a := SimpleGraph.card_neighborFinset_eq_degree G a
        _ ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G a
    · have hempty : Finset.univ.filter (fun e : ↥G.edgeSet => l e = a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e _ hcon
        exact ha (hcon ▸ hls e)
      rw [hempty]
      simp
  have hRb : ∀ b : V, (Finset.univ.filter (fun e : ↥G.edgeSet => r e = b)).card ≤ G.maxDegree := by
    intro b
    by_cases hb : b ∈ t
    · have hle : (Finset.univ.filter (fun e : ↥G.edgeSet => r e = b)).card ≤
          (G.neighborFinset b).card := by
        apply Finset.card_le_card_of_injOn (fun e => l e)
        · intro e he
          have heF : e ∈ Finset.univ.filter (fun e : ↥G.edgeSet => r e = b) := he
          have hrb : r e = b := (Finset.mem_filter.mp heF).2
          have hadj : G.Adj (l e) b := hrb ▸ hadj_lr e
          have hadj2 : G.Adj b (l e) := G.adj_symm hadj
          exact Finset.mem_coe.mpr ((SimpleGraph.mem_neighborFinset G b _).mpr hadj2)
        · intro e₁ he₁ e₂ he₂ hll
          have heF₁ : e₁ ∈ Finset.univ.filter (fun e : ↥G.edgeSet => r e = b) := he₁
          have heF₂ : e₂ ∈ Finset.univ.filter (fun e : ↥G.edgeSet => r e = b) := he₂
          have hr₁ : r e₁ = b := (Finset.mem_filter.mp heF₁).2
          have hr₂ : r e₂ = b := (Finset.mem_filter.mp heF₂).2
          have hr : r e₁ = r e₂ := hr₁.trans hr₂.symm
          exact hor_inj_pair e₁ e₂ hll hr
      calc (Finset.univ.filter (fun e : ↥G.edgeSet => r e = b)).card
          ≤ (G.neighborFinset b).card := hle
        _ = G.degree b := SimpleGraph.card_neighborFinset_eq_degree G b
        _ ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G b
    · have hempty : Finset.univ.filter (fun e : ↥G.edgeSet => r e = b) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e _ hcon
        exact hb (hcon ▸ hrt e)
      rw [hempty]
      simp
  obtain ⟨C, hCL, hCR⟩ := multigraph_bounded_color G.maxDegree V V ↥G.edgeSet l r hLb hRb
  refine ⟨fun e => C ⟨e.val, e.prop⟩, ?_⟩
  intro v w₁ w₂ h₁ h₂ hne hcon
  let e1 : ↥G.edgeSet := ⟨Sym2.mk v w₁, G.mem_edgeSet.mpr h₁⟩
  let e2 : ↥G.edgeSet := ⟨Sym2.mk v w₂, G.mem_edgeSet.mpr h₂⟩
  have hCe : C e1 = C e2 := hcon
  have hmem1 : Sym2.mk (l e1) (r e1) = Sym2.mk v w₁ := by
    have h := hsym e1
    change Sym2.mk (l e1) (r e1) = Sym2.mk v w₁
    exact h.trans rfl
  have hmem2 : Sym2.mk (l e2) (r e2) = Sym2.mk v w₂ := by
    have h := hsym e2
    change Sym2.mk (l e2) (r e2) = Sym2.mk v w₂
    exact h.trans rfl
  have hvst : v ∈ s ∨ v ∈ t := by
    rcases hst.mem_of_adj h₁ with ⟨hvs, _⟩ | ⟨hvt, _⟩
    · exact Or.inl hvs
    · exact Or.inr hvt
  rcases hvst with hvs | hvt
  · have hl1 : l e1 = v := by
      have hiff := Sym2.mk_eq_mk_iff (p := (l e1, r e1)) (q := (v, w₁))
      simp only at hiff
      have heq : (Sym2.mk (l e1) (r e1) : Sym2 V) = Sym2.mk v w₁ := hmem1
      -- rewrite via Prod.mk eta to apply iff
      have heq2 : (s((l e1, r e1).1, (l e1, r e1).2) : Sym2 V) = s((v, w₁).1, (v, w₁).2) := heq
      rcases hiff.mp heq2 with h | h
      · have := congrArg Prod.fst h
        simpa using this
      · have hr_eq : r e1 = v := by
          have := congrArg Prod.snd h
          simpa using this
        exfalso
        have hvt : v ∈ t := hr_eq ▸ hrt e1
        exact (Disjoint.ne_of_mem hst.disjoint hvs hvt) rfl
    have hl2 : l e2 = v := by
      have hiff := Sym2.mk_eq_mk_iff (p := (l e2, r e2)) (q := (v, w₂))
      simp only at hiff
      have heq : (Sym2.mk (l e2) (r e2) : Sym2 V) = Sym2.mk v w₂ := hmem2
      have heq2 : (s((l e2, r e2).1, (l e2, r e2).2) : Sym2 V) = s((v, w₂).1, (v, w₂).2) := heq
      rcases hiff.mp heq2 with h | h
      · have := congrArg Prod.fst h
        simpa using this
      · have hr_eq : r e2 = v := by
          have := congrArg Prod.snd h
          simpa using this
        exfalso
        have hvt : v ∈ t := hr_eq ▸ hrt e2
        exact (Disjoint.ne_of_mem hst.disjoint hvs hvt) rfl
    have heq : e1 = e2 := hCL e1 e2 (hl1.trans hl2.symm) hCe
    have hS : (Sym2.mk v w₁ : Sym2 V) = Sym2.mk v w₂ := congrArg Subtype.val heq
    have hiff := Sym2.mk_eq_mk_iff (p := (v, w₁)) (q := (v, w₂))
    simp only at hiff
    have heq2 : (s((v, w₁).1, (v, w₁).2) : Sym2 V) = s((v, w₂).1, (v, w₂).2) := hS
    rcases hiff.mp heq2 with h | h
    · have hw : w₁ = w₂ := by
        have := congrArg Prod.snd h
        simpa using this
      exact hne hw
    · have hvw2 : v = w₂ := by
        have := congrArg Prod.fst h
        simpa using this
      have hvw1 : w₁ = v := by
        have := congrArg Prod.snd h
        simpa using this
      have hloop : G.Adj v v := hvw2 ▸ h₂
      exact (G.loopless.irrefl v) hloop
  · have hr1 : r e1 = v := by
      have hiff := Sym2.mk_eq_mk_iff (p := (l e1, r e1)) (q := (v, w₁))
      simp only at hiff
      have heq : (Sym2.mk (l e1) (r e1) : Sym2 V) = Sym2.mk v w₁ := hmem1
      have heq2 : (s((l e1, r e1).1, (l e1, r e1).2) : Sym2 V) = s((v, w₁).1, (v, w₁).2) := heq
      rcases hiff.mp heq2 with h | h
      · have hl_eq : l e1 = v := by
          have := congrArg Prod.fst h
          simpa using this
        exfalso
        have hvs2 : v ∈ s := hl_eq ▸ hls e1
        exact (Disjoint.ne_of_mem hst.disjoint hvs2 hvt) rfl
      · have := congrArg Prod.snd h
        simpa using this
    have hr2 : r e2 = v := by
      have hiff := Sym2.mk_eq_mk_iff (p := (l e2, r e2)) (q := (v, w₂))
      simp only at hiff
      have heq : (Sym2.mk (l e2) (r e2) : Sym2 V) = Sym2.mk v w₂ := hmem2
      have heq2 : (s((l e2, r e2).1, (l e2, r e2).2) : Sym2 V) = s((v, w₂).1, (v, w₂).2) := heq
      rcases hiff.mp heq2 with h | h
      · have hl_eq : l e2 = v := by
          have := congrArg Prod.fst h
          simpa using this
        exfalso
        have hvs3 : v ∈ s := hl_eq ▸ hls e2
        exact (Disjoint.ne_of_mem hst.disjoint hvs3 hvt) rfl
      · have := congrArg Prod.snd h
        simpa using this
    have heq : e1 = e2 := hCR e1 e2 (hr1.trans hr2.symm) hCe
    have hS : (Sym2.mk v w₁ : Sym2 V) = Sym2.mk v w₂ := congrArg Subtype.val heq
    have hiff := Sym2.mk_eq_mk_iff (p := (v, w₁)) (q := (v, w₂))
    simp only at hiff
    have heq2 : (s((v, w₁).1, (v, w₁).2) : Sym2 V) = s((v, w₂).1, (v, w₂).2) := hS
    rcases hiff.mp heq2 with h | h
    · have hw : w₁ = w₂ := by
        have := congrArg Prod.snd h
        simpa using this
      exact hne hw
    · have hvw2 : v = w₂ := by
        have := congrArg Prod.fst h
        simpa using this
      have hloop : G.Adj v v := hvw2 ▸ h₂
      exact (G.loopless.irrefl v) hloop

/-- **Proper coloring of unordered pairs.** Let $G$ be a simple graph on $V$. A map $c$ that
assigns a color in $K$ to every unordered pair of elements of $V$ is a proper coloring of
unordered pairs for $G$ when, for all vertices $x, y, z$ such that $x$ is adjacent to both $y$ and
$z$ and $y \ne z$, the pairs $\{x, y\}$ and $\{x, z\}$ receive different colors under $c$.

Only pairs that are edges of $G$ are constrained, so the same map $c$ can be compared across
different graphs on $V$. -/
def IsProperSym2Coloring {V K : Type*} (G : _root_.SimpleGraph V)
    (c : Sym2 V → K) : Prop :=
  ∀ {x y z : V}, G.Adj x y → G.Adj x z → y ≠ z →
    c (Sym2.mk x y) ≠ c (Sym2.mk x z)

/-- **Proper colorings of unordered pairs restrict to proper edge colorings.** Let $G$ be a
simple graph on $V$ and let $c$ assign a color in $K$ to every unordered pair of elements of $V$.
If $c$ is a proper coloring of unordered pairs for $G$, then the edge labeling of $G$ that gives
each edge $e$ the color $c(e)$ is a proper edge coloring of $G$. -/
theorem isProperEdgeColoring_of_isProperSym2Coloring {V K : Type*}
    {G : _root_.SimpleGraph V} {c : Sym2 V → K}
    (hc : IsProperSym2Coloring G c) :
    IsProperEdgeColoring (fun e : G.edgeSet => c e.val) := by
  intro v w₁ w₂ h₁ h₂ hne
  exact hc h₁ h₂ hne

/-- **Proper colorings of unordered pairs pass to subgraphs.** Let $G$ and $H$ be simple graphs
on $V$ such that every edge of $H$ is an edge of $G$. If a map $c$ from unordered pairs of
elements of $V$ to $K$ is a proper coloring of unordered pairs for $G$, then it is also a proper
coloring of unordered pairs for $H$. -/
theorem IsProperSym2Coloring.mono {V K : Type*}
    {G H : _root_.SimpleGraph V}
    {c : Sym2 V → K} (hc : IsProperSym2Coloring G c) (hle : H ≤ G) :
    IsProperSym2Coloring H c := by
  intro x y z h1 h2 hne
  exact hc (hle h1) (hle h2) hne


end MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted
