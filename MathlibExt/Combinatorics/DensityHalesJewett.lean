/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Basic.Real.Basic

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/

@[expose] public section

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace Combinatorics.Line

variable {α ι ι' : Type*}

/-- **Reindexing a combinatorial line.** A combinatorial line $l$ in $\alpha^\iota$ assigns to each
coordinate $i \in \iota$ either a fixed value in $\alpha$ or the free variable, with at least one
free coordinate. Given a bijection $e : \iota \to \iota'$, the reindexing of $l$ along $e$ is the
combinatorial line in $\alpha^{\iota'}$ that assigns to each coordinate $j \in \iota'$ what $l$
assigns to the coordinate $e^{-1}(j)$. -/
public def reindex (l : Line α ι) (e : ι ≃ ι') : Line α ι' where
  idxFun i := l.idxFun (e.symm i)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simpa⟩

/-- **Points of a reindexed line.** Let $l$ be a combinatorial line in $\alpha^\iota$, let
$e : \iota \to \iota'$ be a bijection, and for $a \in \alpha$ write $l(a) \in \alpha^\iota$ for the
point of $l$ whose free coordinates equal $a$. Then for every $a \in \alpha$ and every
$j \in \iota'$, the $j$-th coordinate of the point at $a$ of the reindexing of $l$ along $e$ equals
the $e^{-1}(j)$-th coordinate of $l(a)$. -/
@[simp]
public theorem reindex_apply (l : Line α ι) (e : ι ≃ ι') (a : α) (i : ι') :
    l.reindex e a i = l a (e.symm i) := by
  simp [reindex, Line.coe_apply]

end Combinatorics.Line

namespace Combinatorics.Subspace

variable {η η' α ι ι' : Type*}

/-- **Composition of combinatorial subspaces.** A combinatorial subspace $V$ of $\alpha^\iota$ with
parameter set $\eta$ assigns to each coordinate $i \in \iota$ either a fixed value in $\alpha$ or a
parameter in $\eta$, with every parameter assigned to some coordinate. Let $V$ be such a subspace
and let $W$ be a combinatorial subspace of $\alpha^\eta$ with parameter set $\eta'$. The composite
$V \circ W$ is the combinatorial subspace of $\alpha^\iota$ with parameter set $\eta'$ that assigns
to a coordinate $i$ the fixed value $a$ if $V$ assigns $a$ to $i$, and assigns to $i$ what $W$
assigns to the coordinate $e \in \eta$ if $V$ assigns the parameter $e$ to $i$. -/
public def comp (V : Subspace η α ι) (W : Subspace η' α η) : Subspace η' α ι where
  idxFun i := (V.idxFun i).elim Sum.inl W.idxFun
  proper e := by
    obtain ⟨j, hj⟩ := W.proper e
    obtain ⟨i, hi⟩ := V.proper j
    exact ⟨i, by simp [hi, hj]⟩

/-- **Evaluating a composite subspace.** Let $V$ be a combinatorial subspace of $\alpha^\iota$ with
parameter set $\eta$ and let $W$ be a combinatorial subspace of $\alpha^\eta$ with parameter set
$\eta'$; view each subspace as its map from parameter values to points. Then for every
$x \in \alpha^{\eta'}$, the composite $V \circ W$ sends $x$ to $V(W(x))$. -/
@[simp]
public theorem comp_apply (V : Subspace η α ι) (W : Subspace η' α η) (x : η' → α) :
    V.comp W x = V (W x) := by
  ext i
  cases hi : V.idxFun i <;> simp [comp, Subspace.coe_apply, hi]

/-- **Image of a combinatorial line in a combinatorial subspace.** Let $V$ be a combinatorial
subspace of $\alpha^\iota$ with parameter set $\eta$ and let $l$ be a combinatorial line in
$\alpha^\eta$. The image $V_* l$ is the combinatorial line in $\alpha^\iota$ that has the fixed
value $a$ at each coordinate $i$ to which $V$ assigns the fixed value $a$, and has at each
coordinate $i$ to which $V$ assigns a parameter $e \in \eta$ what $l$ has at the coordinate $e$
(the free variable or a fixed value). -/
public def compLine (V : Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi, he]⟩

/-- **Points of the image of a line.** Let $V$ be a combinatorial subspace of $\alpha^\iota$ with
parameter set $\eta$, viewed as its map $x \mapsto V(x)$ from parameter values to points, and let
$l$ be a combinatorial line in $\alpha^\eta$, with $l(a)$ the point of $l$ whose free coordinates
equal $a$. Then for every $a \in \alpha$, the point at $a$ of the image line $V_* l$ is
$V(l(a))$. -/
@[simp]
public theorem compLine_apply (V : Subspace η α ι) (l : Combinatorics.Line α η) (a : α) :
    V.compLine l a = V (l a) := by
  ext i
  cases hi : V.idxFun i <;> simp [compLine, Subspace.coe_apply, Combinatorics.Line.coe_apply, hi]

/-- **Reindexing commutes with images of lines.** Let $V$ be a combinatorial subspace of
$\alpha^\iota$ with parameter set $\eta$, let $e : \iota \to \iota'$ be a bijection, and let $l$ be
a combinatorial line in $\alpha^\eta$. Let $V^e$ be the combinatorial subspace of $\alpha^{\iota'}$
with parameter set $\eta$ that assigns to each coordinate $j \in \iota'$ what $V$ assigns to the
coordinate $e^{-1}(j)$. Then the image of $l$ under $V^e$ is the reindexing along $e$ of the image
of $l$ under $V$. -/
@[simp]
public theorem reindex_compLine (V : Subspace η α ι) (e : ι ≃ ι')
    (l : Combinatorics.Line α η) :
    (V.reindex (Equiv.refl η) (Equiv.refl α) e).compLine l = (V.compLine l).reindex e := by
  apply Combinatorics.Line.ext
  funext i
  cases hi : V.idxFun (e.symm i) <;>
    simp [compLine, Combinatorics.Line.reindex, Subspace.reindex, hi]

/-- **Images of lines under composite subspaces.** Let $V$ be a combinatorial subspace of
$\alpha^\iota$ with parameter set $\eta$, let $W$ be a combinatorial subspace of $\alpha^\eta$ with
parameter set $\eta'$, and let $l$ be a combinatorial line in $\alpha^{\eta'}$. Then the image of
$l$ under the composite $V \circ W$ equals the image under $V$ of the image of $l$ under $W$, that
is, $(V \circ W)_* l = V_*(W_* l)$. -/
@[simp]
public theorem comp_compLine (V : Subspace η α ι) (W : Subspace η' α η)
    (l : Combinatorics.Line α η') :
    (V.comp W).compLine l = V.compLine (W.compLine l) := by
  apply Combinatorics.Line.ext
  funext i
  cases hi : V.idxFun i <;> simp [comp, compLine, hi]

end Combinatorics.Subspace

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

private def dhjDistinguishedLine {η α : Type*} (x : η → Option α) :
    Combinatorics.Line α (Option η) where
  idxFun
    | none => none
    | some e => x e
  proper := ⟨none, rfl⟩

private def dhjInsertDistinguished {η α ι : Type*}
    (S : Combinatorics.Subspace η (Option α) ι)
    (hstar : ∃ i, S.idxFun i = Sum.inl none) :
    Combinatorics.Subspace (Option η) α ι where
  idxFun i :=
    match S.idxFun i with
    | Sum.inl none => Sum.inr none
    | Sum.inl (some a) => Sum.inl a
    | Sum.inr e => Sum.inr (some e)
  proper e := by
    cases e with
    | none =>
        obtain ⟨i, hi⟩ := hstar
        exact ⟨i, by simp [hi]⟩
    | some e =>
        obtain ⟨i, hi⟩ := S.proper e
        exact ⟨i, by simp [hi]⟩

private theorem dhjInsertDistinguished_compLine_idxFun {η α ι : Type*}
    (S : Combinatorics.Subspace η (Option α) ι)
    (hstar : ∃ i, S.idxFun i = Sum.inl none) (x : η → Option α) :
    ((dhjInsertDistinguished S hstar).compLine (dhjDistinguishedLine x)).idxFun = S x := by
  funext i
  cases hi : S.idxFun i with
  | inl a => cases a <;> simp [dhjInsertDistinguished, dhjDistinguishedLine,
      Combinatorics.Subspace.compLine, Combinatorics.Subspace.coe_apply, hi]
  | inr e => simp [dhjInsertDistinguished, dhjDistinguishedLine,
      Combinatorics.Subspace.compLine, Combinatorics.Subspace.coe_apply, hi]

private theorem dhjGR_oneStar (α κ η : Type*) [Finite α] [Nonempty α] [Finite κ]
    [Finite η] [Nonempty η] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : Combinatorics.Line α ι → κ,
      ∃ V : Combinatorics.Subspace (Option η) α ι, ∃ c : κ,
        ∀ x : η → Option α, C (V.compLine (dhjDistinguishedLine x)) = c := by
  classical
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Subspace.exists_mono_in_high_dimension (Option α) (Option κ) η
  refine ⟨ι, instι, ?_⟩
  intro C
  let color : (ι → Option α) → Option κ := fun w =>
    if h : ∃ i, w i = none then some (C ⟨w, h⟩) else none
  obtain ⟨S, c, hS⟩ := hι color
  have hstar : ∃ i, S.idxFun i = Sum.inl none := by
    by_contra hno
    let a₀ : α := Classical.choice ‹Nonempty α›
    let xSome : η → Option α := fun _ => some a₀
    have hfree : ¬∃ i, S xSome i = none := by
      rintro ⟨i, hi⟩
      cases hidx : S.idxFun i with
      | inl a =>
          cases a with
          | none => exact hno ⟨i, hidx⟩
          | some a => simp [Combinatorics.Subspace.coe_apply, hidx, xSome] at hi
      | inr e => simp [Combinatorics.Subspace.coe_apply, hidx, xSome] at hi
    let e : η := Classical.choice ‹Nonempty η›
    obtain ⟨i, hi⟩ := S.proper e
    let xNone : η → Option α := fun _ => none
    have hproper : ∃ i, S xNone i = none :=
      ⟨i, by rw [Combinatorics.Subspace.apply_inr hi]⟩
    have heq := (hS xSome).trans (hS xNone).symm
    simp [color, hfree, hproper] at heq
  let V := dhjInsertDistinguished S hstar
  let x₀ : η → Option α := fun _ => none
  refine ⟨V, C (V.compLine (dhjDistinguishedLine x₀)), ?_⟩
  intro x
  have hproper (y : η → Option α) : ∃ i, S y i = none := by
    obtain ⟨i, hi⟩ := hstar
    exact ⟨i, by simp [Combinatorics.Subspace.coe_apply, hi]⟩
  let L (y : η → Option α) : Combinatorics.Line α ι := ⟨S y, hproper y⟩
  have hline (y : η → Option α) : V.compLine (dhjDistinguishedLine y) = L y := by
    apply Combinatorics.Line.ext
    exact dhjInsertDistinguished_compLine_idxFun S hstar y
  rw [hline x, hline x₀]
  apply Option.some.inj
  simpa [color, hproper] using (hS x).trans (hS x₀).symm

private def dhjLineTail {α : Type*} {n : ℕ} (l : Combinatorics.Line α (Fin (n + 1)))
    (h : l.idxFun 0 ≠ none) : Combinatorics.Line α (Fin n) where
  idxFun i := l.idxFun i.succ
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    cases i using Fin.cases with
    | zero => exact (h hi).elim
    | succ j => exact ⟨j, hi⟩

private def dhjPrependSubspace {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι) :
    Combinatorics.Subspace (Fin (n + 1)) α (Option ι) where
  idxFun
    | none => Sum.inr 0
    | some i => (W.idxFun i).map id Fin.succ
  proper e := by
    cases e using Fin.cases with
    | zero => exact ⟨none, rfl⟩
    | succ e =>
        obtain ⟨i, hi⟩ := W.proper e
        exact ⟨some i, by simp [hi]⟩

private def dhjPrependLine {α ι : Type*} (a : α) (l : Combinatorics.Line α ι) :
    Combinatorics.Line α (Option ι) where
  idxFun
    | none => some a
    | some i => l.idxFun i
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨some i, hi⟩

private def dhjConsLine {n : ℕ} {α : Type*} (a : α) (l : Combinatorics.Line α (Fin n)) :
    Combinatorics.Line α (Fin (n + 1)) where
  idxFun := Fin.cases (some a) l.idxFun
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i.succ, hi⟩

private theorem dhjConsLine_tail {n : ℕ} {α : Type*}
    (l : Combinatorics.Line α (Fin (n + 1))) (a : α) (h : l.idxFun 0 = some a) :
    dhjConsLine a (dhjLineTail l (by simp [h])) = l := by
  apply Combinatorics.Line.ext
  funext i
  cases i using Fin.cases with
  | zero => exact h.symm
  | succ i => rfl

@[simp]
private theorem dhjLineTail_cons {n : ℕ} {α : Type*}
    (a : α) (l : Combinatorics.Line α (Fin n)) :
    dhjLineTail (dhjConsLine a l) (by simp [dhjConsLine]) = l := by
  apply Combinatorics.Line.ext
  rfl

private def dhjPrefixNormal {α κ : Type} :
    (n : ℕ) → (Q : Type) → (Q → Combinatorics.Line α (Fin n) → κ) → Prop
  | 0, _, _ => True
  | n + 1, Q, C =>
      (∀ q l l', l.idxFun 0 = none → l'.idxFun 0 = none → C q l = C q l') ∧
        dhjPrefixNormal n (Q × α) fun qa l => C qa.1 (dhjConsLine qa.2 l)

private def dhjSamePrefix {α : Type*} :
    (n : ℕ) → Combinatorics.Line α (Fin n) → Combinatorics.Line α (Fin n) → Prop
  | 0, _, _ => True
  | n + 1, l, l' =>
      (l.idxFun 0 = none ∧ l'.idxFun 0 = none) ∨
        ∃ a t t', l = dhjConsLine a t ∧ l' = dhjConsLine a t' ∧ dhjSamePrefix n t t'

private theorem dhjPrefixNormal.eq_of_samePrefix {α κ Q : Type}
    {n : ℕ} {C : Q → Combinatorics.Line α (Fin n) → κ}
    (hC : dhjPrefixNormal n Q C) (q : Q) (l l' : Combinatorics.Line α (Fin n))
    (hll' : dhjSamePrefix n l l') : C q l = C q l' := by
  induction n generalizing Q with
  | zero => exact Fin.elim0 l.proper.choose
  | succ n ih =>
      rcases hll' with h | ⟨a, t, t', rfl, rfl, htt'⟩
      · exact hC.1 q l l' h.1 h.2
      · exact ih hC.2 (q, a) t t' htt'

private theorem dhjPrefixNormal.comap {α κ Q Q' : Type} {n : ℕ}
    {C : Q → Combinatorics.Line α (Fin n) → κ} (hC : dhjPrefixNormal n Q C)
    (f : Q' → Q) : dhjPrefixNormal n Q' fun q l => C (f q) l := by
  induction n generalizing Q Q' with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun q l l' hl hl' => hC.1 (f q) l l' hl hl', ?_⟩
      exact ih hC.2 fun (qa : Q' × α) => (f qa.1, qa.2)

private def dhjPrependWord {β : Type*} {s : ℕ} :
    (r : ℕ) → (Fin r → β) → (Fin s → β) → Fin (s + r) → β
  | 0, _, x => x
  | r + 1, p, x => Fin.cases (p 0) (dhjPrependWord r (fun i => p i.succ) x)

private def dhjTailIndex (s : ℕ) : (r : ℕ) → Fin s → Fin (s + r)
  | 0 => id
  | r + 1 => fun i => (dhjTailIndex s r i).succ

private def dhjPrefixIndex (s : ℕ) : (r : ℕ) → Fin r → Fin (s + r)
  | 0 => Fin.elim0
  | r + 1 => Fin.cases 0 fun i => (dhjPrefixIndex s r i).succ

private theorem dhjPrependWord_tail {β : Type*} {r s : ℕ}
    (p : Fin r → β) (x : Fin s → β) (i : Fin s) :
    dhjPrependWord r p x (dhjTailIndex s r i) = x i := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (fun j => p j.succ)

private theorem dhjPrependWord_prefix {β : Type*} {r s : ℕ}
    (p : Fin r → β) (x : Fin s → β) (i : Fin r) :
    dhjPrependWord r p x (dhjPrefixIndex s r i) = p i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih (fun j => p j.succ) i

private theorem dhjPrependWord_map {β γ : Type*} {r s : ℕ} (f : β → γ)
    (p : Fin r → β) (x : Fin s → β) :
    (fun i => f (dhjPrependWord r p x i)) =
      dhjPrependWord r (f ∘ p) (f ∘ x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact congrFun (ih (fun j => p j.succ)) i

private def dhjPointLine {r s : ℕ} {α : Type*} (p : Fin r → α)
    (l : Combinatorics.Line α (Fin s)) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r (some ∘ p) l.idxFun
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjTailIndex s r i, by simpa [dhjPrependWord_tail]⟩

private def dhjLinePoint {r s : ℕ} {α : Type*} (l : Combinatorics.Line α (Fin r))
    (x : Fin s → α) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r l.idxFun (some ∘ x)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjPrefixIndex s r i, by simpa [dhjPrependWord_prefix]⟩

private def dhjLineWord {r s : ℕ} {α : Type*} (l : Combinatorics.Line α (Fin r))
    (w : Fin s → Option α) : Combinatorics.Line α (Fin (s + r)) where
  idxFun := dhjPrependWord r l.idxFun w
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨dhjPrefixIndex s r i, by simpa [dhjPrependWord_prefix]⟩

private theorem dhjLineWord_of_some {r s : ℕ} {α : Type*}
    (l : Combinatorics.Line α (Fin (r + 1))) (w : Fin s → Option α) (a : α)
    (h : l.idxFun 0 = some a) :
    dhjLineWord l w = dhjConsLine a (dhjLineWord (dhjLineTail l (by simp [h])) w) := by
  apply Combinatorics.Line.ext
  funext i
  cases i using Fin.cases with
  | zero => exact h
  | succ i => rfl

private theorem dhjSamePrefix_lineWord {r s : ℕ} {α : Type*}
    (l : Combinatorics.Line α (Fin r)) (w w' : Fin s → Option α) :
    dhjSamePrefix (s + r) (dhjLineWord l w) (dhjLineWord l w') := by
  induction r generalizing s with
  | zero => exact Fin.elim0 l.proper.choose
  | succ r ih =>
      cases h : l.idxFun 0 with
      | none =>
          exact Or.inl ⟨by simpa [dhjLineWord, dhjPrependWord] using h,
            by simpa [dhjLineWord, dhjPrependWord] using h⟩
      | some a =>
          let t := dhjLineTail l (by simp [h])
          refine Or.inr ⟨a, dhjLineWord t w, dhjLineWord t w', ?_, ?_, ih t w w'⟩
          · exact dhjLineWord_of_some l w a h
          · exact dhjLineWord_of_some l w' a h

private def dhjBlockSubspace {M r s : ℕ} {α : Type*}
    (L : Combinatorics.Line α (Fin r))
    (P : Combinatorics.Subspace (Fin M) α (Fin s)) :
    Combinatorics.Subspace (Fin (M + 1)) α (Fin (s + r)) where
  idxFun := dhjPrependWord r
    (fun i => (L.idxFun i).elim (Sum.inr 0) Sum.inl)
    (fun i => (P.idxFun i).map id Fin.succ)
  proper e := by
    cases e using Fin.cases with
    | zero =>
        obtain ⟨i, hi⟩ := L.proper
        refine ⟨dhjPrefixIndex s r i, ?_⟩
        rw [dhjPrependWord_prefix]
        simp [hi]
    | succ e =>
        obtain ⟨i, hi⟩ := P.proper e
        refine ⟨dhjTailIndex s r i, ?_⟩
        rw [dhjPrependWord_tail]
        simp [hi]

private theorem dhjBlockSubspace_compLine_of_some {M r s : ℕ} {α : Type*}
    (L : Combinatorics.Line α (Fin r))
    (P : Combinatorics.Subspace (Fin M) α (Fin s))
    (u : Combinatorics.Line α (Fin (M + 1))) (a : α) (h : u.idxFun 0 = some a) :
    (dhjBlockSubspace L P).compLine u =
      dhjPointLine (L a) (P.compLine (dhjLineTail u (by simp [h]))) := by
  apply Combinatorics.Line.ext
  change (fun i => (dhjPrependWord r
    (fun j => (L.idxFun j).elim (Sum.inr 0) Sum.inl)
    (fun j => (P.idxFun j).map id Fin.succ) i).elim some u.idxFun) = _
  rw [dhjPrependWord_map]
  simp only [dhjPointLine, Combinatorics.Subspace.compLine]
  congr 1
  · funext i
    cases hi : L.idxFun i <;>
      simp [Combinatorics.Line.coe_apply, hi, h]
  · funext i
    cases hi : P.idxFun i <;>
      simp [dhjLineTail, hi]

private theorem dhjBlockSubspace_compLine_cons {M r s : ℕ} {α : Type*}
    (L : Combinatorics.Line α (Fin r))
    (P : Combinatorics.Subspace (Fin M) α (Fin s)) (a : α)
    (u : Combinatorics.Line α (Fin M)) :
    (dhjBlockSubspace L P).compLine (dhjConsLine a u) =
      dhjPointLine (L a) (P.compLine u) := by
  simpa only [dhjLineTail_cons] using
    dhjBlockSubspace_compLine_of_some L P (dhjConsLine a u) a rfl

private def dhjBlockTailWord {M s : ℕ} {α : Type*}
    (P : Combinatorics.Subspace (Fin M) α (Fin s))
    (u : Combinatorics.Line α (Fin (M + 1))) : Fin s → Option α := fun i =>
  (P.idxFun i).elim some fun e => u.idxFun e.succ

private theorem dhjBlockSubspace_compLine_of_none {M r s : ℕ} {α : Type*}
    (L : Combinatorics.Line α (Fin r))
    (P : Combinatorics.Subspace (Fin M) α (Fin s))
    (u : Combinatorics.Line α (Fin (M + 1))) (h : u.idxFun 0 = none) :
    (dhjBlockSubspace L P).compLine u = dhjLineWord L (dhjBlockTailWord P u) := by
  apply Combinatorics.Line.ext
  change (fun i => (dhjPrependWord r
    (fun j => (L.idxFun j).elim (Sum.inr 0) Sum.inl)
    (fun j => (P.idxFun j).map id Fin.succ) i).elim some u.idxFun) = _
  rw [dhjPrependWord_map]
  simp only [dhjLineWord]
  congr 1
  · funext i
    cases hi : L.idxFun i <;> simp [hi, h]
  · funext i
    cases hi : P.idxFun i <;> simp [dhjBlockTailWord, hi]

private theorem dhjBlockSubspace_samePrefix_of_none {M r s : ℕ} {α : Type*}
    (L : Combinatorics.Line α (Fin r))
    (P : Combinatorics.Subspace (Fin M) α (Fin s))
    (u : Combinatorics.Line α (Fin (M + 1))) (h : u.idxFun 0 = none)
    (x : Fin s → α) :
    dhjSamePrefix (s + r) ((dhjBlockSubspace L P).compLine u) (dhjLinePoint L x) := by
  rw [dhjBlockSubspace_compLine_of_none L P u h]
  apply dhjSamePrefix_lineWord

private def dhjUsesColors {α κ : Type*} :
    (M : ℕ) → (Combinatorics.Line α (Fin M) → κ) → (Fin M → κ) → Prop
  | 0, _, _ => True
  | M + 1, C, c =>
      (∀ u, u.idxFun 0 = none → C u = c 0) ∧
        ∀ a, dhjUsesColors M (fun u => C (dhjConsLine a u)) (fun i => c i.succ)

private theorem dhjUsesColors.eq_of_eq {M : ℕ} {α κ : Type*}
    {C : Combinatorics.Line α (Fin M) → κ} {c : Fin M → κ}
    (hC : dhjUsesColors M C c) (z : κ) (hc : ∀ i, c i = z)
    (u : Combinatorics.Line α (Fin M)) : C u = z := by
  induction M with
  | zero => exact Fin.elim0 u.proper.choose
  | succ M ih =>
      cases h : u.idxFun 0 with
      | none => exact (hC.1 u h).trans (hc 0)
      | some a =>
          rw [← dhjConsLine_tail u a h]
          exact ih (hC.2 a) (fun i : Fin M => hc i.succ) (dhjLineTail u (by simp [h]))

private theorem dhjUsesColors.eq_of_none {M : ℕ} {α κ : Type*}
    {C : Combinatorics.Line α (Fin M) → κ} {c : Fin M → κ}
    (hC : dhjUsesColors M C c) (z : κ) (u : Combinatorics.Line α (Fin M))
    (hc : ∀ i, u.idxFun i = none → c i = z) : C u = z := by
  induction M with
  | zero => exact Fin.elim0 u.proper.choose
  | succ M ih =>
      cases h : u.idxFun 0 with
      | none => exact (hC.1 u h).trans (hc 0 h)
      | some a =>
          rw [← dhjConsLine_tail u a h]
          apply ih (hC.2 a) (dhjLineTail u (by simp [h]))
          intro i hi
          exact hc i.succ hi

private noncomputable def dhjCoordinateSubspace {α : Type*} [Nonempty α] {M m : ℕ}
    (t : Finset (Fin M)) (ht : t.card = m) :
    Combinatorics.Subspace (Fin m) α (Fin M) := by
  let e : t ≃ Fin m := Fintype.equivFinOfCardEq ((Fintype.card_coe t).trans ht)
  exact
    { idxFun := fun i =>
        if h : i ∈ t then Sum.inr (e ⟨i, h⟩)
        else Sum.inl (Classical.choice ‹Nonempty α›)
      proper := by
        intro j
        refine ⟨(e.symm j).1, ?_⟩
        simp [e] }

private theorem dhjCoordinateSubspace_mem_of_compLine_none {α : Type*} [Nonempty α]
    {M m : ℕ} (t : Finset (Fin M)) (ht : t.card = m)
    (l : Combinatorics.Line α (Fin m)) (i : Fin M)
    (hi : ((dhjCoordinateSubspace t ht).compLine l).idxFun i = none) : i ∈ t := by
  by_contra hit
  simp [Combinatorics.Subspace.compLine, dhjCoordinateSubspace, hit] at hi

private theorem dhjUsesColors.congr {M : ℕ} {α κ : Type*}
    {C C' : Combinatorics.Line α (Fin M) → κ} {c : Fin M → κ}
    (hC : dhjUsesColors M C c) (hCC' : ∀ u, C' u = C u) : dhjUsesColors M C' c := by
  induction M with
  | zero => trivial
  | succ M ih =>
      refine ⟨fun u hu => (hCC' u).trans (hC.1 u hu), ?_⟩
      intro a
      exact ih (hC.2 a) fun u => hCC' (dhjConsLine a u)

@[simp]
private theorem dhjPointLine_zero {s : ℕ} {α : Type*}
    (p : Fin 0 → α) (l : Combinatorics.Line α (Fin s)) : dhjPointLine p l = l := by
  apply Combinatorics.Line.ext
  rfl

private theorem dhjPointLine_succ {r s : ℕ} {α : Type*} (p : Fin (r + 1) → α)
    (l : Combinatorics.Line α (Fin s)) :
    dhjPointLine p l = dhjConsLine (p 0) (dhjPointLine (fun i => p i.succ) l) := by
  apply Combinatorics.Line.ext
  rfl

private theorem dhjLinePoint_of_some {r s : ℕ} {α : Type*}
    (l : Combinatorics.Line α (Fin (r + 1))) (x : Fin s → α) (a : α)
    (h : l.idxFun 0 = some a) :
    dhjLinePoint l x = dhjConsLine a (dhjLinePoint (dhjLineTail l (by simp [h])) x) := by
  apply Combinatorics.Line.ext
  funext i
  cases i using Fin.cases with
  | zero => exact h
  | succ i => rfl

private theorem dhjSamePrefix_linePoint {r s : ℕ} {α : Type*}
    (l : Combinatorics.Line α (Fin r)) (x y : Fin s → α) :
    dhjSamePrefix (s + r) (dhjLinePoint l x) (dhjLinePoint l y) := by
  induction r generalizing s with
  | zero => exact Fin.elim0 l.proper.choose
  | succ r ih =>
      cases h : l.idxFun 0 with
      | none =>
          exact Or.inl ⟨by simpa [dhjLinePoint, dhjPrependWord] using h,
            by simpa [dhjLinePoint, dhjPrependWord] using h⟩
      | some a =>
          let t := dhjLineTail l (by simp [h])
          refine Or.inr ⟨a, dhjLinePoint t x, dhjLinePoint t y, ?_, ?_, ih t x y⟩
          · exact dhjLinePoint_of_some l x a h
          · exact dhjLinePoint_of_some l y a h

private theorem dhjLineHJFin (α κ : Type) [Finite α] [Finite κ] :
    ∃ n : ℕ, ∀ C : (Fin n → α) → κ,
      ∃ l : Combinatorics.Line α (Fin n), ∃ c : κ, ∀ a, C (l a) = c := by
  obtain ⟨ι, instι, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension α κ
  let _ : Fintype ι := instι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, ?_⟩
  intro C
  obtain ⟨l, c, hc⟩ := hι fun x => C (x ∘ e.symm)
  refine ⟨l.reindex e, c, ?_⟩
  intro a
  rw [← hc a]
  congr 1

private theorem dhjPrefixNormal.pointLine {α κ Q : Type} {r s : ℕ}
    {C : Q → Combinatorics.Line α (Fin (s + r)) → κ}
    (hC : dhjPrefixNormal (s + r) Q C) (p : Fin r → α) :
    dhjPrefixNormal s Q fun q l => C q (dhjPointLine p l) := by
  induction r generalizing Q with
  | zero => simpa only [Nat.add_zero, dhjPointLine_zero] using hC
  | succ r ih =>
      have h := ih hC.2 (fun i => p i.succ)
      have h' := h.comap fun q : Q => (q, p 0)
      simpa only [dhjPointLine_succ] using h'

private def dhjTailWord {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι)
    (l : Combinatorics.Line α (Fin (n + 1))) : ι → Option α := fun i =>
  (W.idxFun i).elim some fun e => l.idxFun e.succ

private theorem dhjPrependSubspace_compLine_of_none {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι)
    (l : Combinatorics.Line α (Fin (n + 1))) (h : l.idxFun 0 = none) :
    (dhjPrependSubspace W).compLine l = dhjDistinguishedLine (dhjTailWord W l) := by
  apply Combinatorics.Line.ext
  funext i
  cases i with
  | none => simpa [dhjPrependSubspace, Combinatorics.Subspace.compLine,
      dhjDistinguishedLine] using h
  | some i =>
      cases hi : W.idxFun i <;>
        simp [dhjPrependSubspace, Combinatorics.Subspace.compLine,
          dhjDistinguishedLine, dhjTailWord, hi]

private theorem dhjPrependSubspace_compLine_of_some {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι)
    (l : Combinatorics.Line α (Fin (n + 1))) (a : α) (h : l.idxFun 0 = some a) :
    (dhjPrependSubspace W).compLine l =
      dhjPrependLine a (W.compLine (dhjLineTail l (by simp [h]))) := by
  apply Combinatorics.Line.ext
  funext i
  cases i with
  | none => simpa [dhjPrependSubspace, Combinatorics.Subspace.compLine,
      dhjPrependLine] using h
  | some i =>
      cases hi : W.idxFun i <;>
        simp [dhjPrependSubspace, Combinatorics.Subspace.compLine,
          dhjPrependLine, dhjLineTail, hi]

private theorem dhjPrependSubspace_compLine_cons {n : ℕ} {α ι : Type*}
    (W : Combinatorics.Subspace (Fin n) α ι) (a : α)
    (l : Combinatorics.Line α (Fin n)) :
    (dhjPrependSubspace W).compLine (dhjConsLine a l) =
      dhjPrependLine a (W.compLine l) := by
  apply Combinatorics.Line.ext
  funext i
  cases i with
  | none => rfl
  | some i =>
      cases hi : W.idxFun i <;>
        simp [dhjPrependSubspace, Combinatorics.Subspace.compLine,
          dhjPrependLine, dhjConsLine, hi]

private theorem dhjGR_prefix_normal (α κ : Type) [Finite α] [Nonempty α] [Finite κ]
    [Nonempty κ] (n : ℕ) :
    ∀ (Q : Type) [Finite Q] [Nonempty Q],
      ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι),
        ∀ C : Q → Combinatorics.Line α ι → κ,
          ∃ T : Combinatorics.Subspace (Fin n) α ι,
            dhjPrefixNormal n Q fun q l => C q (T.compLine l) := by
  induction n with
  | zero =>
      intro Q _ _
      refine ⟨Unit, inferInstance, inferInstance, ?_⟩
      intro C
      let a₀ : α := Classical.choice ‹Nonempty α›
      let T : Combinatorics.Subspace (Fin 0) α Unit :=
        ⟨fun _ => Sum.inl a₀, fun e => Fin.elim0 e⟩
      exact ⟨T, trivial⟩
  | succ n ih =>
      intro Q _ _
      obtain ⟨ι, instι, nonemptyι, hι⟩ := ih (Q × α)
      let _ : Fintype ι := instι
      let _ : Nonempty ι := nonemptyι
      obtain ⟨I, instI, hI⟩ := dhjGR_oneStar α (Q → κ) ι
      let _ : Fintype I := instI
      have nonemptyI : Nonempty I := by
        let k₀ : κ := Classical.choice ‹Nonempty κ›
        obtain ⟨V, c, hV⟩ := hI fun _ _ => k₀
        obtain ⟨i, hi⟩ := V.proper none
        exact ⟨i⟩
      refine ⟨I, instI, nonemptyI, ?_⟩
      intro C
      obtain ⟨V, c, hV⟩ := hI fun l q => C q l
      let Ctail : Q × α → Combinatorics.Line α ι → κ := fun qa l =>
        C qa.1 (V.compLine (dhjPrependLine qa.2 l))
      obtain ⟨W, hW⟩ := hι Ctail
      let T := V.comp (dhjPrependSubspace W)
      refine ⟨T, ?_, ?_⟩
      · intro q l l' hl hl'
        dsimp only [T]
        rw [Combinatorics.Subspace.comp_compLine, Combinatorics.Subspace.comp_compLine,
          dhjPrependSubspace_compLine_of_none W l hl,
          dhjPrependSubspace_compLine_of_none W l' hl']
        exact (congrFun (hV (dhjTailWord W l)) q).trans
          (congrFun (hV (dhjTailWord W l')) q).symm
      · simpa only [T, Ctail, Combinatorics.Subspace.comp_compLine,
          dhjPrependSubspace_compLine_cons] using hW

private theorem dhjGR_blocks (α κ : Type) [Finite α] [Nonempty α] [Finite κ]
    [Nonempty κ] (M : ℕ) :
    ∃ R : ℕ, ∀ C : Combinatorics.Line α (Fin R) → κ,
      dhjPrefixNormal R Unit (fun _ l => C l) →
        ∃ P : Combinatorics.Subspace (Fin M) α (Fin R), ∃ c : Fin M → κ,
          dhjUsesColors M (fun u => C (P.compLine u)) c := by
  classical
  induction M with
  | zero =>
      refine ⟨0, ?_⟩
      intro C hC
      let P : Combinatorics.Subspace (Fin 0) α (Fin 0) :=
        ⟨Fin.elim0, fun e => Fin.elim0 e⟩
      exact ⟨P, Fin.elim0, trivial⟩
  | succ M ih =>
      obtain ⟨s, hs⟩ := ih
      let _ : Finite (Combinatorics.Line α (Fin s)) :=
        Finite.of_injective (fun l : Combinatorics.Line α (Fin s) => l.idxFun)
          fun _ _ h => Combinatorics.Line.ext h
      obtain ⟨r, hr⟩ := dhjLineHJFin α (Combinatorics.Line α (Fin s) → κ)
      refine ⟨s + r, ?_⟩
      intro C hC
      obtain ⟨L, g, hL⟩ := hr fun p l => C (dhjPointLine p l)
      let a₀ : α := Classical.choice ‹Nonempty α›
      let p₀ := L a₀
      have hTail := dhjPrefixNormal.pointLine hC p₀
      obtain ⟨P, c, hP⟩ := hs (fun l => C (dhjPointLine p₀ l)) (by simpa using hTail)
      let B := dhjBlockSubspace L P
      let x₀ := P fun _ => a₀
      let z := C (dhjLinePoint L x₀)
      let c' : Fin (M + 1) → κ := Fin.cases z c
      refine ⟨B, c', ?_, ?_⟩
      · intro u hu
        have hsame := dhjBlockSubspace_samePrefix_of_none L P u hu x₀
        have heq := hC.eq_of_samePrefix () (B.compLine u) (dhjLinePoint L x₀) hsame
        simpa [c', z] using heq
      · intro a
        apply hP.congr
        intro u
        dsimp only [B]
        rw [dhjBlockSubspace_compLine_cons]
        exact (congrFun (hL a) (P.compLine u)).trans
          (congrFun (hL a₀) (P.compLine u)).symm

private theorem dhjGR_fin (α κ : Type) [Finite α] [Nonempty α] [Finite κ]
    [Nonempty κ] (m : ℕ) :
    ∃ N : ℕ, ∀ C : Combinatorics.Line α (Fin N) → κ,
      ∃ V : Combinatorics.Subspace (Fin m) α (Fin N), ∃ z : κ,
        ∀ l : Combinatorics.Line α (Fin m), C (V.compLine l) = z := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  let M := Fintype.card κ * m
  obtain ⟨R, hR⟩ := dhjGR_blocks α κ M
  obtain ⟨I, instI, nonemptyI, hI⟩ := dhjGR_prefix_normal α κ R Unit
  let _ : Fintype I := instI
  let _ : Nonempty I := nonemptyI
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_⟩
  intro C
  let C' : Combinatorics.Line α I → κ := fun l => C (l.reindex e)
  obtain ⟨T, hT⟩ := hI fun _ l => C' l
  obtain ⟨P, c, hP⟩ := hR (fun l => C' (T.compLine l)) hT
  obtain ⟨z, hz⟩ := Fintype.exists_le_card_fiber_of_mul_le_card c (n := m) (by
    simp [M])
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hz
  let Q := dhjCoordinateSubspace (α := α) t htcard
  let V₀ := T.comp (P.comp Q)
  let V := V₀.reindex (Equiv.refl (Fin m)) (Equiv.refl α) e
  refine ⟨V, z, ?_⟩
  intro l
  have hcolor : C' (T.compLine (P.compLine (Q.compLine l))) = z := by
    apply hP.eq_of_none z (Q.compLine l)
    intro i hi
    have hit : i ∈ t := dhjCoordinateSubspace_mem_of_compLine_none t htcard l i hi
    exact (Finset.mem_filter.mp (ht hit)).2
  dsimp only [V]
  rw [Combinatorics.Subspace.reindex_compLine]
  change C' (V₀.compLine l) = z
  simpa only [V₀, Combinatorics.Subspace.comp_compLine] using hcolor

universe u v

/--
**Graham–Rothschild theorem for combinatorial lines.** Let $\alpha$ be a finite nonempty alphabet,
let $\kappa$ be a finite nonempty set of colors and let $m$ be a natural number. Then there is a
natural number $N$ such that for every coloring $C$ of the combinatorial lines in $\alpha^N$ with
colors in $\kappa$ there are a combinatorial subspace $V$ of $\alpha^N$ with parameter set
$\{0, \dots, m - 1\}$ and a color $z \in \kappa$ such that for every combinatorial line $l$ in
$\alpha^m$, the image $V_* l$ of $l$ in $V$ satisfies $C(V_* l) = z$.
-/
public theorem _root_.Combinatorics.Subspace.exists_lines_mono_in_high_dimension_fin
    (α : Type u) (κ : Type v) [Finite α] [Nonempty α] [Finite κ] [Nonempty κ] (m : ℕ) :
    ∃ N : ℕ, ∀ C : Combinatorics.Line α (Fin N) → κ,
      ∃ V : Combinatorics.Subspace (Fin m) α (Fin N), ∃ z : κ,
        ∀ l : Combinatorics.Line α (Fin m), C (V.compLine l) = z := by
  classical
  let eα := Finite.equivFin α
  let eκ := Finite.equivFin κ
  let _ : Nonempty (Fin (Nat.card α)) := Nonempty.map eα ‹Nonempty α›
  let _ : Nonempty (Fin (Nat.card κ)) := Nonempty.map eκ ‹Nonempty κ›
  obtain ⟨N, hN⟩ := dhjGR_fin (Fin (Nat.card α)) (Fin (Nat.card κ)) m
  refine ⟨N, ?_⟩
  intro C
  let C' : Combinatorics.Line (Fin (Nat.card α)) (Fin N) → Fin (Nat.card κ) :=
    fun l => eκ (C (l.map eα.symm))
  obtain ⟨V₀, z, hV₀⟩ := hN C'
  let V := V₀.reindex (Equiv.refl (Fin m)) eα.symm (Equiv.refl (Fin N))
  refine ⟨V, eκ.symm z, ?_⟩
  intro l
  have hline : (V₀.compLine (l.map eα)).map eα.symm = V.compLine l := by
    apply Combinatorics.Line.ext
    funext i
    cases hi : V₀.idxFun i <;>
      simp [V, Combinatorics.Subspace.compLine, Combinatorics.Subspace.reindex,
        Combinatorics.Line.map, hi]
  apply eκ.injective
  simpa [C', hline] using hV₀ (l.map eα)

private noncomputable def dhjDensity {X : Type*} [Fintype X] (A : Finset X) : ℝ :=
  A.card / Fintype.card X

private def dhjConcat {α ι κ : Type*} (x : ι → α) (y : κ → α) : ι ⊕ κ → α :=
  Sum.elim x y

private noncomputable def dhjSection {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) := by
  classical
  exact Finset.univ.filter fun y => dhjConcat x y ∈ A

private theorem dhj_card_eq_sum_sections {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ] [Fintype (ι → α)]
    (A : Finset (ι ⊕ κ → α)) :
    A.card = ∑ x : ι → α, (dhjSection A x).card := by
  classical
  let e := Equiv.sumArrowEquivProdArrow ι κ α
  let B := A.map e.toEmbedding
  calc
    A.card = B.card := by simp [B]
    _ = ∑ x ∈ Finset.univ, ({p ∈ B | p.1 = x}).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      simp
    _ = ∑ x : ι → α, (dhjSection A x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      symm
      apply Finset.card_bij (fun y _ => (x, y))
      · intro y hy
        simp only [dhjSection, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rw [Finset.mem_filter]
        refine ⟨?_, rfl⟩
        dsimp only [B]
        rw [Finset.mem_map]
        exact ⟨dhjConcat x y, hy, rfl⟩
      · intro y₁ hy₁ y₂ hy₂ h
        exact congrArg Prod.snd h
      · intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨hpB, hpx⟩ := hp
        refine ⟨p.2, ?_, ?_⟩
        · simp only [dhjSection, Finset.mem_filter, Finset.mem_univ, true_and]
          obtain ⟨w, hw, hew⟩ := Finset.mem_map.mp hpB
          subst p
          rw [← hpx]
          have hrecombine : dhjConcat (e w).1 (e w).2 = w := by
            ext j
            cases j <;> rfl
          change dhjConcat (e w).1 (e w).2 ∈ A
          rw [hrecombine]
          exact hw
        · exact Prod.ext hpx.symm rfl

private theorem dhj_density_eq_average_sections {α ι κ : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [Fintype κ]
    [Fintype (ι → α)] [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) :
    dhjDensity A =
      (∑ x : ι → α, dhjDensity (dhjSection A x)) / Fintype.card (ι → α) := by
  classical
  let e := Equiv.sumArrowEquivProdArrow ι κ α
  have hcard : Fintype.card (ι ⊕ κ → α) =
      Fintype.card (ι → α) * Fintype.card (κ → α) := by
    exact (Fintype.card_congr e).trans (Fintype.card_prod _ _)
  simp only [dhjDensity, dhj_card_eq_sum_sections A, Nat.cast_sum, hcard, Nat.cast_mul]
  rw [← Finset.sum_div]
  rw [div_div]
  congr 1
  exact mul_comm _ _

private theorem dhj_density_eq_expect_sections {α ι κ : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [Fintype κ]
    [Fintype (ι → α)] [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) :
    dhjDensity A = Finset.expect Finset.univ fun x : ι → α => dhjDensity (dhjSection A x) := by
  rw [Fintype.expect_eq_sum_div_card]
  exact dhj_density_eq_average_sections A

private theorem dhjDensity_map_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (A : Finset X) :
    dhjDensity (A.map e.toEmbedding) = dhjDensity A := by
  classical
  simp [dhjDensity, Fintype.card_congr e]

private def dhjPrefixLine {α ι κ : Type*} (x : ι → α)
    (l : Combinatorics.Line α κ) : Combinatorics.Line α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => some (x i)
    | Sum.inr j => l.idxFun j
  proper := by
    obtain ⟨j, hj⟩ := l.proper
    exact ⟨Sum.inr j, hj⟩

@[simp]
private theorem dhjPrefixLine_apply {α ι κ : Type*} (x : ι → α)
    (l : Combinatorics.Line α κ) (a : α) :
    dhjPrefixLine x l a = dhjConcat x (l a) := by
  ext i
  cases i <;> simp [dhjPrefixLine, dhjConcat, Combinatorics.Line.coe_apply]

private def dhjLineIn {α ι : Type*} (A : Finset (ι → α))
    (l : Combinatorics.Line α ι) : Prop := ∀ a, l a ∈ A

private noncomputable instance dhjFiniteLine {α ι : Type*} [Finite α] [Finite ι] :
    Finite (Combinatorics.Line α ι) :=
  Finite.of_injective Combinatorics.Line.idxFun fun _ _ h => Combinatorics.Line.ext h

private noncomputable instance dhjFintypeLine {α ι : Type*} [Fintype α] [Fintype ι] :
    Fintype (Combinatorics.Line α ι) := Fintype.ofFinite _

private noncomputable instance dhjFiniteSubspace {η α ι : Type*}
    [Finite η] [Finite α] [Finite ι] :
    Finite (Combinatorics.Subspace η α ι) :=
  Finite.of_injective Combinatorics.Subspace.idxFun fun _ _ h =>
    Combinatorics.Subspace.ext h

private noncomputable instance dhjFintypeSubspace {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype ι] :
    Fintype (Combinatorics.Subspace η α ι) := Fintype.ofFinite _

private theorem dhjSubspace_apply_injective {η α ι : Type*}
    (V : Combinatorics.Subspace η α ι) : Function.Injective V := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  have hi' := congrFun hxy i
  simpa [Combinatorics.Subspace.coe_apply, hi] using hi'

private noncomputable def dhjSubspacePoints {η α ι : Type*}
    [Fintype η] [Fintype α] (V : Combinatorics.Subspace η α ι) :
    Finset (ι → α) := by
  classical
  exact Finset.univ.map ⟨V, dhjSubspace_apply_injective V⟩

@[simp]
private theorem dhj_mem_subspacePoints {η α ι : Type*}
    [Fintype η] [Fintype α] (V : Combinatorics.Subspace η α ι) (w : ι → α) :
    w ∈ dhjSubspacePoints V ↔ ∃ x : η → α, V x = w := by
  classical
  simp [dhjSubspacePoints]

@[simp]
private theorem dhj_card_subspacePoints {η α ι : Type*}
    [Fintype η] [Fintype α] (V : Combinatorics.Subspace η α ι) :
    (dhjSubspacePoints V).card = Fintype.card α ^ Fintype.card η := by
  classical
  simp [dhjSubspacePoints]

private inductive dhjTiled (d k : ℕ) {ι : Type*}
    [DecidableEq (ι → Fin (k + 1))] :
    Finset (ι → Fin (k + 1)) → Prop
  | empty : dhjTiled d k ∅
  | add (C : Finset (ι → Fin (k + 1)))
      (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) ι) :
      dhjTiled d k C → Disjoint C (dhjSubspacePoints V) →
        dhjTiled d k (C ∪ dhjSubspacePoints V)

private noncomputable def dhjLineCount (k n : ℕ) : ℕ :=
  Nat.card (Combinatorics.Line (Fin k) (Fin n))

private theorem dhjLineCount_pos {k n : ℕ} (hn : 0 < n) : 0 < dhjLineCount k n := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Nat.card_pos

private def dhjLiftLine {k : ℕ} {ι : Type*} (l : Combinatorics.Line (Fin k) ι) :
    Combinatorics.Line (Fin (k + 1)) ι where
  idxFun i := (l.idxFun i).map Fin.castSucc
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi]⟩

@[simp]
private theorem dhjLiftLine_apply {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) (a : Fin k) :
    dhjLiftLine l (Fin.castSucc a) = Fin.castSucc ∘ l a := by
  funext i
  cases hi : l.idxFun i <;>
    simp [dhjLiftLine, Combinatorics.Line.coe_apply, hi]

private def dhjLineTop {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) : ι → Fin (k + 1) :=
  dhjLiftLine l (Fin.last k)

private def dhjHasLast {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1)) : Prop :=
  ¬∀ i, x i ≠ Fin.last k

private theorem dhjLineTop_hasLast {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) : dhjHasLast (dhjLineTop l) := by
  obtain ⟨i, hi⟩ := l.proper
  intro h
  exact h i (by simp [dhjLineTop, dhjLiftLine, Combinatorics.Line.coe_apply, hi])

private def dhjLineOfTop {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1))
    (hx : dhjHasLast x) : Combinatorics.Line (Fin k) ι where
  idxFun i := Fin.lastCases none some (x i)
  proper := by
    rw [dhjHasLast] at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by simp [hi]⟩

@[simp]
private theorem dhjLineTop_lineOfTop {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1))
    (hx : dhjHasLast x) : dhjLineTop (dhjLineOfTop x hx) = x := by
  funext i
  generalize hxi : x i = a
  cases a using Fin.lastCases <;>
    simp [dhjLineTop, dhjLiftLine, dhjLineOfTop, Combinatorics.Line.coe_apply, hxi]

@[simp]
private theorem dhjLineOfTop_lineTop {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) :
    dhjLineOfTop (dhjLineTop l) (dhjLineTop_hasLast l) = l := by
  apply Combinatorics.Line.ext
  funext i
  cases hi : l.idxFun i <;>
    simp [dhjLineOfTop, dhjLineTop, dhjLiftLine, Combinatorics.Line.coe_apply, hi]

private def dhjLineTopEquiv {k : ℕ} {ι : Type*} :
    Combinatorics.Line (Fin k) ι ≃ {x : ι → Fin (k + 1) // dhjHasLast x} where
  toFun l := ⟨dhjLineTop l, dhjLineTop_hasLast l⟩
  invFun x := dhjLineOfTop x x.2
  left_inv := dhjLineOfTop_lineTop
  right_inv x := by
    apply Subtype.ext
    exact dhjLineTop_lineOfTop x.1 x.2

private def dhjNoLastEquiv {k : ℕ} {ι : Type*} :
    {x : ι → Fin (k + 1) // ∀ i, x i ≠ Fin.last k} ≃ (ι → Fin k) where
  toFun x i := (x.1 i).castPred (x.2 i)
  invFun x := ⟨Fin.castSucc ∘ x, fun i => Fin.castSucc_ne_last _⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.castSucc_castPred _ _
  right_inv x := by
    funext i
    exact Fin.castPred_castSucc _

private theorem dhjLineCount_eq (k m : ℕ) :
    dhjLineCount k m = (k + 1) ^ m - k ^ m := by
  classical
  rw [dhjLineCount, Nat.card_eq_fintype_card,
    Fintype.card_congr (dhjLineTopEquiv (k := k) (ι := Fin m))]
  let e : {x : Fin m → Fin (k + 1) // dhjHasLast x} ≃
      {x : Fin m → Fin (k + 1) // ¬∀ i, x i ≠ Fin.last k} :=
    Equiv.subtypeEquivRight fun _ => by simp only [dhjHasLast]
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl]
  rw [Fintype.card_congr (dhjNoLastEquiv (k := k) (ι := Fin m))]
  simp

private theorem dhj_two_mul_pow_le_succ_pow {k m : ℕ} (hk : 0 < k) (hm : k ≤ m) :
    2 * k ^ m ≤ (k + 1) ^ m := by
  have hbaseRaw := pow_add_mul_le_add_pow (R := ℕ) (a := k) (b := 1)
    (Nat.zero_le k) (by omega : 0 ≤ 2 * k + 1) k
  have hkpow : k * k ^ (k - 1) = k ^ k := by
    calc
      k * k ^ (k - 1) = k ^ ((k - 1) + 1) := (pow_succ' k (k - 1)).symm
      _ = k ^ k := by congr 1; omega
  have hbase : 2 * k ^ k ≤ (k + 1) ^ k := by
    simpa [hkpow, two_mul] using hbaseRaw
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, pow_add]
  calc
    2 * (k ^ k * k ^ r) = (2 * k ^ k) * k ^ r := by ring
    _ ≤ (k + 1) ^ k * k ^ r := Nat.mul_le_mul_right _ hbase
    _ ≤ (k + 1) ^ k * (k + 1) ^ r := by
      gcongr
      omega

private theorem dhj_half_cube_le_lineCount {k m : ℕ} (hk : 0 < k) (hm : k ≤ m) :
    (k + 1) ^ m ≤ 2 * dhjLineCount k m := by
  rw [dhjLineCount_eq]
  have hpow := dhj_two_mul_pow_le_succ_pow hk hm
  have hle : k ^ m ≤ (k + 1) ^ m := Nat.pow_le_pow_left (by omega) m
  omega

private def dhjAt (k n : ℕ) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ ≤ dhjDensity A →
    ∃ l : Combinatorics.Line (Fin k) (Fin n), dhjLineIn A l

private theorem dhjAt.mono_dimension {k N n : ℕ} {δ : ℝ}
    (hk : 0 < k) (hN : dhjAt k N δ) (hNn : N ≤ n) : dhjAt k n δ := by
  classical
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro A hA
  have hadd : n - N + N = n := Nat.sub_add_cancel hNn
  let e : Fin (n - N) ⊕ Fin N ≃ Fin n := finSumFinEquiv.trans (finCongr hadd)
  let we : (Fin n → Fin k) ≃ (Fin (n - N) ⊕ Fin N → Fin k) :=
    Equiv.arrowCongr e.symm (Equiv.refl (Fin k))
  let A' := A.map we.toEmbedding
  have hdens : dhjDensity A' = dhjDensity A := dhjDensity_map_equiv we A
  have havg : δ ≤ Finset.expect Finset.univ
      (fun x : Fin (n - N) → Fin k => dhjDensity (dhjSection A' x)) := by
    rw [← dhj_density_eq_expect_sections A', hdens]
    exact hA
  obtain ⟨x, hxuniv, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  obtain ⟨l, hl⟩ := hN (dhjSection A' x) hx
  let L := dhjPrefixLine x l
  refine ⟨L.reindex e, ?_⟩
  intro a
  have hconcat : dhjConcat x (l a) ∈ A' := by
    simpa [dhjSection] using hl a
  obtain ⟨w, hw, hwe⟩ := Finset.mem_map.mp hconcat
  have hre : L.reindex e a = w := by
    apply we.injective
    change we w = dhjConcat x (l a) at hwe
    rw [hwe]
    funext q
    change L.reindex e a (e q) = dhjConcat x (l a) q
    rw [Combinatorics.Line.reindex_apply, Equiv.symm_apply_apply,
      dhjPrefixLine_apply]
  rw [hre]
  exact hw

private def dhjThreshold (k : ℕ) (δ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, dhjAt k n δ

private theorem dhjThreshold_of_at {k N : ℕ} {δ : ℝ} (hk : 0 < k) (h : dhjAt k N δ) :
    dhjThreshold k δ := by
  exact ⟨N, fun _ hn => h.mono_dimension hk hn⟩

private theorem dhjDensity_nonneg {X : Type*} [Fintype X] (A : Finset X) :
    0 ≤ dhjDensity A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem dhjDensity_le_one {X : Type*} [Fintype X] [Nonempty X]
    (A : Finset X) : dhjDensity A ≤ 1 := by
  rw [dhjDensity, div_le_one (by positivity)]
  exact_mod_cast A.card_le_univ

private theorem dhjDensity_mono {X : Type*} [Fintype X] {A B : Finset X}
    (hAB : A ⊆ B) : dhjDensity A ≤ dhjDensity B := by
  unfold dhjDensity
  gcongr

@[simp]
private theorem dhjDensity_univ {X : Type*} [Fintype X] [Nonempty X] :
    dhjDensity (Finset.univ : Finset X) = 1 := by
  simp [dhjDensity]

@[simp]
private theorem dhjDensity_empty {X : Type*} [Fintype X] :
    dhjDensity (∅ : Finset X) = 0 := by
  simp [dhjDensity]

private theorem dhjDensity_sdiff_add {X : Type*} [Fintype X] [DecidableEq X]
    {A B : Finset X} (hBA : B ⊆ A) :
    dhjDensity (A \ B) + dhjDensity B = dhjDensity A := by
  simp only [dhjDensity, ← add_div, ← Nat.cast_add]
  rw [Finset.card_sdiff_add_card_eq_card hBA]

private noncomputable def dhjPullback {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x => V x ∈ A

private noncomputable def dhjDensityOn {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (A : Finset (ι → α)) (V : Combinatorics.Subspace η α ι) : ℝ :=
  dhjDensity (dhjPullback V A)

private def dhjSubspaceIn {η α ι : Type*} (A : Finset (ι → α))
    (V : Combinatorics.Subspace η α ι) : Prop := ∀ x, V x ∈ A

@[simp]
private theorem dhj_mem_pullback {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) (x : η → α) :
    x ∈ dhjPullback V A ↔ V x ∈ A := by
  classical
  simp [dhjPullback]

private theorem dhjLineIn_compLine_iff {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α))
    (l : Combinatorics.Line α η) :
    dhjLineIn A (V.compLine l) ↔ dhjLineIn (dhjPullback V A) l := by
  simp [dhjLineIn]

private theorem dhjPullback_comp {η η' α ι : Type*}
    [Fintype η] [Fintype η'] [Fintype α]
    [Fintype (η → α)] [Fintype (η' → α)]
    (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace η' α η)
    (A : Finset (ι → α)) :
    dhjPullback (V.comp W) A = dhjPullback W (dhjPullback V A) := by
  classical
  ext x
  simp

private theorem dhjDensityOn_comp {η η' α ι : Type*}
    [Fintype η] [Fintype η'] [Fintype α]
    [Fintype (η → α)] [Fintype (η' → α)]
    (A : Finset (ι → α)) (V : Combinatorics.Subspace η α ι)
    (W : Combinatorics.Subspace η' α η) :
    dhjDensityOn A (V.comp W) = dhjDensityOn (dhjPullback V A) W := by
  simp [dhjDensityOn, dhjPullback_comp]

private theorem dhj_one_le_wallis (n : ℕ) : 1 ≤ Real.Wallis.W n := by
  induction n with
  | zero => simp [Real.Wallis.W]
  | succ n ih =>
      rw [Real.Wallis.W_succ]
      have hfactor : (1 : ℝ) ≤
          ((2 * n + 2) / (2 * n + 1)) * ((2 * n + 2) / (2 * n + 3)) := by
        rw [div_mul_div_comm]
        rw [one_le_div₀ (by positivity)]
        nlinarith
      exact ih.trans (le_mul_of_one_le_right (Real.Wallis.W_pos n).le hfactor)

private theorem dhj_centralBinom_sq_mul_le (n : ℕ) :
    (Nat.centralBinom n : ℝ) ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  have hw := dhj_one_le_wallis n
  rw [Real.Wallis.W_eq_factorial_ratio] at hw
  have hden : (0 : ℝ) < ((2 * n).factorial : ℝ) ^ 2 * (2 * n + 1) := by positivity
  have hraw := (le_div_iff₀ hden).mp hw
  have hfacNat : Nat.centralBinom n * n.factorial * n.factorial =
      (2 * n).factorial := by
    have hsub : 2 * n - n = n := by omega
    have hchoose := Nat.choose_mul_factorial_mul_factorial
      (Nat.le_mul_of_pos_left n zero_lt_two)
    rw [hsub] at hchoose
    simpa [Nat.centralBinom] using hchoose
  have hfac : (Nat.centralBinom n : ℝ) * n.factorial * n.factorial =
      ((2 * n).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [← hfac] at hraw
  have hf : (0 : ℝ) < (n.factorial : ℝ) ^ 4 := by positivity
  have hmul :
      ((Nat.centralBinom n : ℝ) ^ 2 * (2 * n + 1)) * (n.factorial : ℝ) ^ 4 ≤
        (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 4 := by
    calc
      _ = ((Nat.centralBinom n : ℝ) * n.factorial * n.factorial) ^ 2 *
          (2 * n + 1) := by ring
      _ ≤ 2 ^ (4 * n) * (n.factorial : ℝ) ^ 4 := by simpa using hraw
      _ = (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 4 := by
        congr 1
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
  exact le_of_mul_le_mul_right hmul hf

private theorem dhj_centralBinom_ratio_sq_le (n : ℕ) :
    ((Nat.centralBinom n : ℝ) / 4 ^ n) ^ 2 ≤ 1 / (2 * n + 1) := by
  rw [div_pow, div_le_div_iff₀ (by positivity : (0 : ℝ) < (4 ^ n) ^ 2) (by positivity)]
  simp only [one_mul]
  have h := dhj_centralBinom_sq_mul_le n
  calc
    _ ≤ (16 : ℝ) ^ n := h
    _ = (4 : ℝ) ^ (2 * n) := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
    _ = (4 : ℝ) ^ (n * 2) := by rw [Nat.mul_comm]
    _ = ((4 : ℝ) ^ n) ^ 2 := pow_mul 4 n 2

private theorem dhj_exists_centralBinom_ratio_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (Nat.centralBinom n : ℝ) / 4 ^ n < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ ^ 2)
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hlarge : 1 / δ ^ 2 < (2 * n + 1 : ℝ) := by
    have hnle : n ≤ 2 * n + 1 := by omega
    exact hn.trans_le (by exact_mod_cast hnle)
  have hone : 1 < δ ^ 2 * (2 * n + 1 : ℝ) := by
    have := (div_lt_iff₀ hδsq).mp hlarge
    nlinarith
  have hsmall : 1 / (2 * n + 1 : ℝ) < δ ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    exact hone
  have hsquare := (dhj_centralBinom_ratio_sq_le n).trans_lt hsmall
  refine ⟨n, ?_⟩
  have hratio : 0 ≤ (Nat.centralBinom n : ℝ) / 4 ^ n := by positivity
  nlinarith

private def dhjSupport {ι : Type*} [Fintype ι] (x : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i => x i = 1

@[simp]
private theorem dhj_mem_support {ι : Type*} [Fintype ι] (x : ι → Fin 2) (i : ι) :
    i ∈ dhjSupport x ↔ x i = 1 := by
  simp [dhjSupport]

private theorem dhjSupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (dhjSupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [dhj_mem_support] using Finset.ext_iff.mp hxy i
  apply Fin.ext
  omega

private def dhjLineOfSupport {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : Combinatorics.Line (Fin 2) ι where
  idxFun i := if x i = y i then some (x i) else none
  proper := by
    obtain ⟨i, hiy, hix⟩ := Finset.exists_of_ssubset hxy
    have hne : x i ≠ y i := by
      intro hi
      have hy : y i = 1 := dhj_mem_support y i |>.mp hiy
      exact hix (dhj_mem_support x i |>.mpr (hi.trans hy))
    exact ⟨i, by simp [hne]⟩

@[simp]
private theorem dhjLineOfSupport_zero {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : dhjLineOfSupport x y hxy 0 = x := by
  funext i
  by_cases hi : x i = y i
  · simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hi]
  · have hsub := hxy.1
    have hx : x i ≠ 1 := by
      intro hx
      have hy := hsub (dhj_mem_support x i |>.mpr hx)
      exact hi (hx.trans (dhj_mem_support y i |>.mp hy).symm)
    have hx0 : x i = 0 := by
      apply Fin.ext
      omega
    have hne : (0 : Fin 2) ≠ y i := by
      intro h
      exact hi (hx0.trans h)
    simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hx0, hne]

@[simp]
private theorem dhjLineOfSupport_one {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : dhjLineOfSupport x y hxy 1 = y := by
  funext i
  by_cases hi : x i = y i
  · simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hi]
  · have hsub := hxy.1
    have himp : x i = 1 → y i = 1 := by
      intro hx
      exact dhj_mem_support y i |>.mp (hsub (dhj_mem_support x i |>.mpr hx))
    have hy : y i = 1 := by
      apply Fin.ext
      omega
    have hx : x i ≠ 1 := by
      intro hx
      exact hi (hx.trans hy.symm)
    simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hy, hx]

private def dhjLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ¬dhjLineIn A l

private theorem dhj_supports_antichain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (ι → Fin 2)) (hA : dhjLineFree A) :
    IsAntichain (· ⊆ ·) (A.image dhjSupport : Set (Finset ι)) := by
  classical
  rintro s hs t ht hst hsub
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
  have hproper : dhjSupport x ⊂ dhjSupport y :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hst⟩
  apply hA (dhjLineOfSupport x y hproper)
  intro a
  fin_cases a
  · simpa using hx
  · simpa using hy

private theorem dhj_lineFree_card_le_middle {n : ℕ} (A : Finset (Fin n → Fin 2))
    (hA : dhjLineFree A) : A.card ≤ n.choose (n / 2) := by
  classical
  have hsperner := (dhj_supports_antichain A hA).sperner
  rw [Finset.card_image_of_injective A dhjSupport_injective] at hsperner
  simpa using hsperner

private theorem dhj_lineFree_density_le_central (r : ℕ)
    (A : Finset (Fin (2 * r) → Fin 2)) (hA : dhjLineFree A) :
    dhjDensity A ≤ (Nat.centralBinom r : ℝ) / 4 ^ r := by
  have hcard : A.card ≤ Nat.centralBinom r := by
    simpa [Nat.centralBinom, Nat.mul_div_cancel_left] using dhj_lineFree_card_le_middle A hA
  have hcube : Fintype.card (Fin (2 * r) → Fin 2) = 4 ^ r := by
    simp [pow_mul]
  rw [dhjDensity, hcube]
  rw [Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast hcard

private theorem dhjThreshold_two {δ : ℝ} (hδ : 0 < δ) : dhjThreshold 2 δ := by
  obtain ⟨r, hr⟩ := dhj_exists_centralBinom_ratio_lt hδ
  apply dhjThreshold_of_at (k := 2) (N := 2 * r) (by omega)
  intro A hden
  by_contra hline
  have hfree : dhjLineFree A := by
    intro l hl
    exact hline ⟨l, hl⟩
  have hupper := dhj_lineFree_density_le_central r A hfree
  linarith

private noncomputable def dhjDensePrefixes {α ι κ : Type*}
    [Fintype α] [Fintype ι] [Fintype κ]
    [Fintype (ι → α)] [Fintype (κ → α)]
    (A : Finset (ι ⊕ κ → α)) (δ : ℝ) : Finset (ι → α) := by
  classical
  exact Finset.univ.filter fun x => δ / 2 ≤ dhjDensity (dhjSection A x)

private theorem dhjDensity_densePrefixes {α ι κ : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [Fintype κ]
    [Fintype (ι → α)] [Fintype (κ → α)] [Fintype (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) {δ : ℝ} (hδ : 0 < δ) (hA : δ ≤ dhjDensity A) :
    δ / 2 ≤ dhjDensity (dhjDensePrefixes A δ) := by
  classical
  let B := dhjDensePrefixes A δ
  let f : (ι → α) → ℝ := fun x => dhjDensity (dhjSection A x)
  have hpoint : ∀ x ∈ (Finset.univ : Finset (ι → α)),
      f x ≤ δ / 2 + if x ∈ B then 1 else 0 := by
    intro x hx
    by_cases hxB : x ∈ B
    · simp only [hxB, ↓reduceIte]
      have hf := dhjDensity_le_one (dhjSection A x)
      linarith
    · simp only [hxB, ↓reduceIte, add_zero]
      have : ¬δ / 2 ≤ f x := by
        simpa [B, dhjDensePrefixes, f] using hxB
      exact le_of_lt (lt_of_not_ge this)
  have hsumUpper :
      (∑ x : ι → α, f x) ≤
        Fintype.card (ι → α) * (δ / 2) + B.card := by
    calc
      (∑ x : ι → α, f x) ≤
          ∑ x : ι → α, (δ / 2 + if x ∈ B then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
      _ = Fintype.card (ι → α) * (δ / 2) + B.card := by
        rw [Finset.sum_add_distrib]
        simp
  have hsumLower : δ * Fintype.card (ι → α) ≤ ∑ x : ι → α, f x := by
    rw [dhj_density_eq_average_sections] at hA
    rw [le_div_iff₀ (by positivity)] at hA
    simpa [f, mul_comm] using hA
  change δ / 2 ≤ (B.card : ℝ) / Fintype.card (ι → α)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

private theorem dhj_exists_dense_fiber {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (B : Finset X) (f : X → Y) :
    ∃ y : Y, dhjDensity B / Fintype.card Y ≤
      dhjDensity (B.filter fun x => f x = y) := by
  classical
  have hsum : dhjDensity B =
      ∑ y : Y, dhjDensity (B.filter fun x => f x = y) := by
    simp only [dhjDensity]
    have hcard : B.card = ∑ y : Y, (B.filter fun x => f x = y).card :=
      Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
    rw [hcard, Nat.cast_sum, Finset.sum_div]
  have havg : dhjDensity B / Fintype.card Y =
      Finset.expect Finset.univ fun y : Y =>
        dhjDensity (B.filter fun x => f x = y) := by
    rw [Fintype.expect_eq_sum_div_card, ← hsum]
  obtain ⟨y, hy, hfy⟩ := Finset.exists_le_of_le_expect
    (s := (Finset.univ : Finset Y)) Finset.univ_nonempty (le_of_eq havg)
  exact ⟨y, hfy⟩

private def dhjExtendSubspace {η α ι κ : Type*}
    (U : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α κ) :
    Combinatorics.Subspace (η ⊕ Unit) α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => (U.idxFun i).map id Sum.inl
    | Sum.inr j => (l.idxFun j).elim (Sum.inr (Sum.inr ())) Sum.inl
  proper
    | Sum.inl e => by
        obtain ⟨i, hi⟩ := U.proper e
        exact ⟨Sum.inl i, by simp [hi]⟩
    | Sum.inr _ => by
        obtain ⟨j, hj⟩ := l.proper
        exact ⟨Sum.inr j, by simp [hj]⟩

@[simp]
private theorem dhjExtendSubspace_apply {η α ι κ : Type*}
    (U : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α κ)
    (x : η → α) (a : α) :
    dhjExtendSubspace U l (Sum.elim x fun _ => a) = dhjConcat (U x) (l a) := by
  ext q
  cases q with
  | inl i =>
      cases h : U.idxFun i <;>
        simp [dhjExtendSubspace, dhjConcat, Combinatorics.Subspace.coe_apply, h]
  | inr j =>
      cases h : l.idxFun j <;>
        simp [dhjExtendSubspace, dhjConcat, Combinatorics.Subspace.coe_apply,
          Combinatorics.Line.coe_apply, h]

private def dhjPointSubspace {α ι : Type*} (x : ι → α) :
    Combinatorics.Subspace (Fin 0) α ι where
  idxFun i := Sum.inl (x i)
  proper e := Fin.elim0 e

@[simp]
private theorem dhjPointSubspace_apply {α ι : Type*} (x : ι → α) (z : Fin 0 → α) :
    dhjPointSubspace x z = x := by
  ext i
  simp [dhjPointSubspace, Combinatorics.Subspace.coe_apply]

private def dhjMultiAt (k m n : ℕ) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ ≤ dhjDensity A →
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), dhjSubspaceIn A V

private theorem dhjMultiAt_zero {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    dhjMultiAt k 0 0 δ := by
  intro A hA
  have hne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hA
    simp at hA
    linarith
  obtain ⟨x, hx⟩ := hne
  exact ⟨dhjPointSubspace x, fun z => by simpa using hx⟩

private theorem dhjMultiAt_succ {k m P M : ℕ} {δ : ℝ}
    (hk : 0 < k) (hMpos : 0 < M) (hδ : 0 < δ)
    (hLine : dhjAt k M (δ / 2))
    (hMulti : dhjMultiAt k m P (δ / (2 * dhjLineCount k M))) :
    dhjMultiAt k (m + 1) (P + M) δ := by
  classical
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let _ : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
  let _ : Fintype (Combinatorics.Line (Fin k) (Fin M)) := Fintype.ofFinite _
  intro A hA
  let e : Fin P ⊕ Fin M ≃ Fin (P + M) := finSumFinEquiv
  let we : (Fin (P + M) → Fin k) ≃ (Fin P ⊕ Fin M → Fin k) :=
    Equiv.arrowCongr e.symm (Equiv.refl (Fin k))
  let A' := A.map we.toEmbedding
  have hA'dens : dhjDensity A' = dhjDensity A := dhjDensity_map_equiv we A
  let B := dhjDensePrefixes A' δ
  have hB : δ / 2 ≤ dhjDensity B := by
    apply dhjDensity_densePrefixes A' hδ
    simpa [hA'dens] using hA
  have hLineAt (x : Fin P → Fin k) (hx : x ∈ B) :
      ∃ l : Combinatorics.Line (Fin k) (Fin M), dhjLineIn (dhjSection A' x) l := by
    apply hLine
    exact (Finset.mem_filter.mp hx).2
  let chosen : (Fin P → Fin k) → Combinatorics.Line (Fin k) (Fin M) := fun x =>
    if hx : x ∈ B then Classical.choose (hLineAt x hx) else default
  have hchosen (x : Fin P → Fin k) (hx : x ∈ B) :
      dhjLineIn (dhjSection A' x) (chosen x) := by
    simpa only [chosen, dite_eq_left hx] using Classical.choose_spec (hLineAt x hx)
  obtain ⟨l, hl⟩ := dhj_exists_dense_fiber B chosen
  let D := B.filter fun x => chosen x = l
  have hcount : Fintype.card (Combinatorics.Line (Fin k) (Fin M)) =
      dhjLineCount k M := by
    simp [dhjLineCount, Nat.card_eq_fintype_card]
  have hD : δ / (2 * dhjLineCount k M) ≤ dhjDensity D := by
    calc
      δ / (2 * dhjLineCount k M) =
          (δ / 2) / Fintype.card (Combinatorics.Line (Fin k) (Fin M)) := by
        rw [hcount]
        field_simp
      _ ≤ dhjDensity B / Fintype.card (Combinatorics.Line (Fin k) (Fin M)) := by
        gcongr
      _ ≤ dhjDensity D := by simpa [D] using hl
  obtain ⟨U, hU⟩ := hMulti D hD
  let W := dhjExtendSubspace U l
  let eη : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    (Equiv.sumCongr (Equiv.refl (Fin m)) (Equiv.ofUnique Unit (Fin 1))).trans
      finSumFinEquiv
  let V := W.reindex eη (Equiv.refl (Fin k)) e
  refine ⟨V, ?_⟩
  intro z
  let x : Fin m → Fin k := fun i => z (eη (Sum.inl i))
  let a : Fin k := z (eη (Sum.inr ()))
  have hUD : U x ∈ D := hU x
  have hUB : U x ∈ B := (Finset.mem_filter.mp hUD).1
  have hUl : chosen (U x) = l := (Finset.mem_filter.mp hUD).2
  have hsec := hchosen (U x) hUB a
  have hconcat : dhjConcat (U x) (l a) ∈ A' := by
    have : dhjConcat (U x) (chosen (U x) a) ∈ A' := by
      simpa [dhjSection] using hsec
    rwa [hUl] at this
  obtain ⟨w, hw, hwe⟩ := Finset.mem_map.mp hconcat
  have hzvar : (fun q => z (eη q)) = Sum.elim x (fun _ => a) := by
    funext q
    cases q <;> rfl
  have hW : W (fun q => z (eη q)) = dhjConcat (U x) (l a) := by
    rw [hzvar]
    exact dhjExtendSubspace_apply U l x a
  have hmap : we (V z) = W (fun q => z (eη q)) := by
    funext q
    simp [we, V, e, Function.comp_def]
  have hvw : V z = w := by
    apply we.injective
    calc
      we (V z) = W (fun q => z (eη q)) := hmap
      _ = dhjConcat (U x) (l a) := hW
      _ = we w := hwe.symm
  rwa [hvw]

private theorem dhjMultiThreshold {k : ℕ} (hk : 0 < k)
    (hDHJ : ∀ δ : ℝ, 0 < δ → dhjThreshold k δ) :
    ∀ (m : ℕ) (δ : ℝ), 0 < δ → ∃ N : ℕ, dhjMultiAt k m N δ := by
  intro m
  induction m with
  | zero =>
      intro δ hδ
      exact ⟨0, dhjMultiAt_zero hδ⟩
  | succ m ih =>
      intro δ hδ
      obtain ⟨N₀, hN₀⟩ := hDHJ (δ / 2) (by positivity)
      let M := N₀ + 1
      have hMpos : 0 < M := by simp [M]
      have hLine : dhjAt k M (δ / 2) := hN₀ M (by simp [M])
      have hcount : 0 < dhjLineCount k M := dhjLineCount_pos hMpos
      have heps : 0 < δ / (2 * dhjLineCount k M) := by positivity
      obtain ⟨P, hP⟩ := ih (δ / (2 * dhjLineCount k M)) heps
      exact ⟨P + M, dhjMultiAt_succ hk hMpos hδ hLine hP⟩

private def dhjAppend {X : Type*} {t : ℕ} (p : Fin t → X) (x : X) : Fin (t + 1) → X :=
  Fin.lastCases x p

private def dhjBlockAgrees {X : Type*} {L t : ℕ} (p : Fin t → X) (h : t ≤ L)
    (w : Fin L → X) : Prop := ∀ i, w (Fin.castLE h i) = p i

private noncomputable def dhjCylinder {X : Type*} {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) : Finset (Fin L → X) := by
  classical
  exact A.filter (dhjBlockAgrees p h)

private theorem dhjBlockAgrees_append {X : Type*} {L t : ℕ}
    (p : Fin t → X) (x : X) (h : t + 1 ≤ L) (w : Fin L → X) :
    dhjBlockAgrees (dhjAppend p x) h w ↔
      dhjBlockAgrees p (Nat.le_trans (Nat.le_add_right t 1) h) w ∧
        w ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) h⟩ = x := by
  constructor
  · intro hw
    constructor
    · intro i
      simpa [dhjAppend, dhjBlockAgrees] using hw (Fin.castSucc i)
    · have hidx : Fin.castLE h (Fin.last t) =
          (⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) h⟩ : Fin L) := by
        apply Fin.ext
        rfl
      have hlast := hw (Fin.last t)
      rw [hidx] at hlast
      simpa [dhjAppend, dhjBlockAgrees] using hlast
  · rintro ⟨hp, hx⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hidx : Fin.castLE h (Fin.last t) =
          (⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) h⟩ : Fin L) := by
        apply Fin.ext
        rfl
      rw [hidx]
      simpa [dhjAppend, dhjBlockAgrees] using hx
    · simpa [dhjAppend, dhjBlockAgrees] using hp j

private theorem dhjCylinder_append {X : Type*} {L t : ℕ} [DecidableEq X]
    (A : Finset (Fin L → X)) (p : Fin t → X) (x : X) (h : t + 1 ≤ L) :
    dhjCylinder A (dhjAppend p x) h =
      (dhjCylinder A p (Nat.le_trans (Nat.le_add_right t 1) h)).filter fun w =>
        w ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) h⟩ = x := by
  classical
  ext w
  simp only [dhjCylinder, Finset.mem_filter]
  rw [dhjBlockAgrees_append]
  tauto

private theorem dhj_card_cylinder_eq_sum_append {X : Type*} {L t : ℕ} [Fintype X]
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t + 1 ≤ L) :
    (dhjCylinder A p (Nat.le_trans (Nat.le_add_right t 1) h)).card =
      ∑ x : X, (dhjCylinder A (dhjAppend p x) h).card := by
  classical
  let C := dhjCylinder A p (Nat.le_trans (Nat.le_add_right t 1) h)
  let next : (Fin L → X) → X := fun w =>
    w ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) h⟩
  have hcard : C.card = ∑ x : X, (C.filter fun w => next w = x).card :=
    Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)
  rw [hcard]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact (dhjCylinder_append A p x h).symm

private noncomputable def dhjCylinderDensity {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) : ℝ :=
  (dhjCylinder A p h).card / (Fintype.card X : ℝ) ^ (L - t)

private theorem dhj_sum_cylinderDensity_append {X : Type*} {L t : ℕ}
    [Fintype X] [Nonempty X] (A : Finset (Fin L → X)) (p : Fin t → X)
    (h : t + 1 ≤ L) :
    (∑ x : X, dhjCylinderDensity A (dhjAppend p x) h) =
      Fintype.card X *
        dhjCylinderDensity A p (Nat.le_trans (Nat.le_add_right t 1) h) := by
  classical
  have hsub : L - t = (L - (t + 1)) + 1 := by omega
  have hq : (Fintype.card X : ℝ) ≠ 0 := by positivity
  simp only [dhjCylinderDensity]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← dhj_card_cylinder_eq_sum_append]
  rw [hsub, pow_succ]
  field_simp

private theorem dhjCylinderDensity_zero {X : Type*} {L : ℕ} [Fintype X]
    (A : Finset (Fin L → X)) :
    dhjCylinderDensity A (Fin.elim0 : Fin 0 → X) (Nat.zero_le L) = dhjDensity A := by
  classical
  have hcyl : dhjCylinder A (Fin.elim0 : Fin 0 → X) (Nat.zero_le L) = A := by
    ext w
    simp [dhjCylinder, dhjBlockAgrees]
  rw [dhjCylinderDensity, hcyl, dhjDensity]
  simp

private theorem dhjCylinderDensity_full_le_one {X : Type*} {L : ℕ} [Fintype X]
    (A : Finset (Fin L → X)) (p : Fin L → X) :
    dhjCylinderDensity A p (le_refl L) ≤ 1 := by
  classical
  have hcard : (dhjCylinder A p (le_refl L)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro w hw v hv
    apply funext
    intro i
    have hw' := (Finset.mem_filter.mp hw).2 i
    have hv' := (Finset.mem_filter.mp hv).2 i
    exact hw'.trans hv'.symm
  simpa [dhjCylinderDensity] using hcard

private theorem dhj_exists_average_increment {X : Type*} [Fintype X] [Nonempty X]
    (hq : 2 ≤ Fintype.card X) (f : X → ℝ) {a μ ε : ℝ} (hε : 0 < ε)
    (ha : a ≤ μ) (havg : (∑ x : X, f x) = Fintype.card X * μ)
    (hlow : ∃ x, f x < a - ε) :
    ∃ y, μ + ε / (Fintype.card X - 1) ≤ f y := by
  classical
  obtain ⟨x, hx⟩ := hlow
  by_contra h
  simp only [not_exists, not_le] at h
  have herase := Finset.sum_le_card_nsmul (Finset.univ.erase x) f
    (μ + ε / (Fintype.card X - 1)) fun y hy => (h y).le
  have hcardErase : (Finset.univ.erase x).card = Fintype.card X - 1 := by simp
  rw [hcardErase] at herase
  simp only [nsmul_eq_mul] at herase
  have hq1 : 0 < Fintype.card X - 1 := by omega
  have hq1R : (0 : ℝ) < (Fintype.card X - 1 : ℕ) := by exact_mod_cast hq1
  have hrho : ((Fintype.card X - 1 : ℕ) : ℝ) *
      (ε / (Fintype.card X - 1 : ℕ)) = ε := by
    field_simp
  have hdecomp : (∑ y : X, f y) = f x + ∑ y ∈ Finset.univ.erase x, f y := by
    rw [add_comm]
    exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ x)).symm
  rw [hdecomp] at havg
  norm_num only [Nat.cast_sub (by omega : 1 ≤ Fintype.card X), Nat.cast_one] at herase hrho
  nlinarith

private theorem dhj_exists_regular_cylinder {X : Type*} [Fintype X] [Nonempty X]
    (hq : 2 ≤ Fintype.card X) (R : ℕ) (A : Finset (Fin (R + 1) → X))
    {ε : ℝ} (hε : 0 < ε)
    (hR : 1 < (R + 1) * (ε / (Fintype.card X - 1))) :
    ∃ (t : ℕ) (ht : t ≤ R) (p : Fin t → X),
      ∀ x : X, dhjDensity A - ε ≤
        dhjCylinderDensity A (dhjAppend p x) (by omega) := by
  classical
  let ρ : ℝ := ε / (Fintype.card X - 1)
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    apply div_pos hε
    have hcardR : (1 : ℝ) < Fintype.card X := by
      exact_mod_cast (show 1 < Fintype.card X by omega)
    linarith
  by_contra hgood
  have hbad (t : ℕ) (ht : t ≤ R) (p : Fin t → X) :
      ∃ x : X, dhjCylinderDensity A (dhjAppend p x) (by omega) < dhjDensity A - ε := by
    by_contra h
    push Not at h
    exact hgood ⟨t, ht, p, h⟩
  have hchain : ∀ (t : ℕ) (ht : t ≤ R + 1),
      ∃ p : Fin t → X,
        dhjDensity A + t * ρ ≤ dhjCylinderDensity A p ht := by
    intro t
    induction t with
    | zero =>
        intro ht
        refine ⟨Fin.elim0, ?_⟩
        simpa using (dhjCylinderDensity_zero A).ge
    | succ t ih =>
        intro ht
        have htR : t ≤ R := by omega
        obtain ⟨p, hp⟩ := ih (by omega)
        let f : X → ℝ := fun x =>
          dhjCylinderDensity A (dhjAppend p x) ht
        have havg : (∑ x : X, f x) = Fintype.card X *
            dhjCylinderDensity A p (by omega) := by
          simpa [f] using dhj_sum_cylinderDensity_append A p ht
        have ha : dhjDensity A ≤ dhjCylinderDensity A p (by omega) := by
          have htρ : 0 ≤ (t : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ.le
          linarith
        obtain ⟨x, hx⟩ := dhj_exists_average_increment hq f hε ha havg (hbad t htR p)
        refine ⟨dhjAppend p x, ?_⟩
        change dhjDensity A + (t + 1 : ℕ) * ρ ≤ f x
        dsimp only [ρ] at hx ⊢
        push_cast
        nlinarith
  obtain ⟨p, hp⟩ := hchain (R + 1) (le_refl _)
  have hle := dhjCylinderDensity_full_le_one A p
  have hnonneg := dhjDensity_nonneg A
  dsimp only [ρ] at hp
  push_cast at hp hR
  nlinarith

private def dhjFinSplit {L t : ℕ} (h : t ≤ L) : Fin t ⊕ Fin (L - t) ≃ Fin L :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

private def dhjBlockJoin {X : Type*} {L t : ℕ} (p : Fin t → X)
    (y : Fin (L - t) → X) (h : t ≤ L) : Fin L → X :=
  dhjConcat p y ∘ (dhjFinSplit h).symm

private noncomputable def dhjBlockSection {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) :
    Finset (Fin (L - t) → X) := by
  classical
  exact Finset.univ.filter fun y => dhjBlockJoin p y h ∈ A

@[simp]
private theorem dhjBlockJoin_split_left {X : Type*} {L t : ℕ} (p : Fin t → X)
    (y : Fin (L - t) → X) (h : t ≤ L) (i : Fin t) :
    dhjBlockJoin p y h (dhjFinSplit h (Sum.inl i)) = p i := by
  simp [dhjBlockJoin, dhjFinSplit, dhjConcat]

@[simp]
private theorem dhjBlockJoin_split_right {X : Type*} {L t : ℕ} (p : Fin t → X)
    (y : Fin (L - t) → X) (h : t ≤ L) (j : Fin (L - t)) :
    dhjBlockJoin p y h (dhjFinSplit h (Sum.inr j)) = y j := by
  simp [dhjBlockJoin, dhjFinSplit, dhjConcat]

private theorem dhj_card_blockSection {X : Type*} [Fintype X] {L t : ℕ}
    (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) :
    (dhjBlockSection A p h).card = (dhjCylinder A p h).card := by
  classical
  apply Finset.card_bij (fun y _ => dhjBlockJoin p y h)
  · intro y hy
    simp only [dhjCylinder, Finset.mem_filter]
    constructor
    · exact (Finset.mem_filter.mp (show y ∈ dhjBlockSection A p h from hy)).2
    · intro i
      exact dhjBlockJoin_split_left p y h i
  · intro y₁ hy₁ y₂ hy₂ heq
    funext j
    have := congrFun heq (dhjFinSplit h (Sum.inr j))
    simpa using this
  · intro w hw
    let y : Fin (L - t) → X := fun j => w (dhjFinSplit h (Sum.inr j))
    have hjoin : dhjBlockJoin p y h = w := by
      funext i
      have hi := (dhjFinSplit h).apply_symm_apply i
      rw [← hi]
      cases hq : (dhjFinSplit h).symm i with
      | inl j =>
          rw [dhjBlockJoin_split_left]
          exact ((Finset.mem_filter.mp hw).2 j).symm
      | inr j => simp [y]
    refine ⟨y, ?_, hjoin⟩
    simp only [dhjBlockSection, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hjoin]
    exact (Finset.mem_filter.mp (show w ∈ dhjCylinder A p h from hw)).1

private theorem dhjDensity_blockSection_eq_cylinderDensity {X : Type*} [Fintype X]
    {L t : ℕ} (A : Finset (Fin L → X)) (p : Fin t → X) (h : t ≤ L) :
    dhjDensity (dhjBlockSection A p h) = dhjCylinderDensity A p h := by
  rw [dhjDensity, dhjCylinderDensity, dhj_card_blockSection]
  simp

private theorem dhj_exists_regular_blockSection {X : Type*} [Fintype X] [Nonempty X]
    (hq : 2 ≤ Fintype.card X) (R : ℕ) (A : Finset (Fin (R + 1) → X))
    {ε : ℝ} (hε : 0 < ε)
    (hR : 1 < (R + 1) * (ε / (Fintype.card X - 1))) :
    ∃ (t : ℕ) (ht : t ≤ R) (p : Fin t → X),
      ∀ x : X, dhjDensity A - ε ≤
        dhjDensity (dhjBlockSection A (dhjAppend p x) (by omega)) := by
  obtain ⟨t, ht, p, hp⟩ := dhj_exists_regular_cylinder hq R A hε hR
  exact ⟨t, ht, p, fun x => by
    rw [dhjDensity_blockSection_eq_cylinderDensity]
    exact hp x⟩

private theorem dhj_exists_regular_length {X : Type*} [Fintype X] [Nonempty X]
    (hq : 2 ≤ Fintype.card X) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 1 < (R + 1) * (ε / (Fintype.card X - 1)) := by
  let ρ : ℝ := ε / (Fintype.card X - 1)
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    apply div_pos hε
    have hcardR : (1 : ℝ) < Fintype.card X := by exact_mod_cast (show 1 < Fintype.card X by omega)
    linarith
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / ρ)
  refine ⟨R, ?_⟩
  have hmul : 1 < (R : ℝ) * ρ := (div_lt_iff₀ hρ).mp (by simpa using hR)
  nlinarith

private def dhjBlockPrefixSubspace {α : Type*} {r t : ℕ}
    (p : Fin t → Fin r → α) :
    Combinatorics.Subspace (Fin r) α (Fin (t + 1) × Fin r) where
  idxFun q := Fin.lastCases (Sum.inr q.2) (fun i => Sum.inl (p i q.2)) q.1
  proper j := ⟨(Fin.last t, j), by simp⟩

@[simp]
private theorem dhjBlockPrefixSubspace_apply {α : Type*} {r t : ℕ}
    (p : Fin t → Fin r → α) (x : Fin r → α) (q : Fin (t + 1) × Fin r) :
    dhjBlockPrefixSubspace p x q = dhjAppend p x q.1 q.2 := by
  rcases q with ⟨b, j⟩
  refine Fin.lastCases ?_ (fun i => ?_) b
  · simp [dhjBlockPrefixSubspace, dhjAppend, Combinatorics.Subspace.coe_apply]
  · simp [dhjBlockPrefixSubspace, dhjAppend, Combinatorics.Subspace.coe_apply]

private noncomputable def dhjColumn {X Ω : Type*} [Fintype X] [Fintype Ω]
    (E : X → Finset Ω) (ω : Ω) : Finset X := by
  classical
  exact Finset.univ.filter fun x => ω ∈ E x

private theorem dhj_sum_card_rows_eq_sum_card_columns {X Ω : Type*}
    [Fintype X] [Fintype Ω] (E : X → Finset Ω) :
    (∑ x : X, (E x).card) = ∑ ω : Ω, (dhjColumn E ω).card := by
  classical
  simp only [Finset.card_eq_sum_ones, dhjColumn, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

private theorem dhj_average_density_rows_eq_columns {X Ω : Type*}
    [Fintype X] [Nonempty X] [Fintype Ω] [Nonempty Ω] (E : X → Finset Ω) :
    (∑ x : X, dhjDensity (E x)) / Fintype.card X =
      (∑ ω : Ω, dhjDensity (dhjColumn E ω)) / Fintype.card Ω := by
  have hcards := dhj_sum_card_rows_eq_sum_card_columns E
  simp only [dhjDensity, ← Finset.sum_div]
  rw [div_div, div_div]
  congr 1
  · exact_mod_cast hcards
  · ring

private noncomputable def dhjDenseColumns {X Ω : Type*} [Fintype X] [Fintype Ω]
    (E : X → Finset Ω) (α : ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => α / 2 ≤ dhjDensity (dhjColumn E ω)

private theorem dhjDensity_denseColumns {X Ω : Type*}
    [Fintype X] [Nonempty X] [Fintype Ω] [Nonempty Ω]
    (E : X → Finset Ω) {α : ℝ} (hα : 0 < α)
    (hE : ∀ x, α ≤ dhjDensity (E x)) :
    α / 2 ≤ dhjDensity (dhjDenseColumns E α) := by
  classical
  let B := dhjDenseColumns E α
  let f : Ω → ℝ := fun ω => dhjDensity (dhjColumn E ω)
  have hrows : α ≤ (∑ x : X, dhjDensity (E x)) / Fintype.card X := by
    rw [le_div_iff₀ (by positivity)]
    have hs := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset X)) => hE x
    simpa [mul_comm] using hs
  have havg : α ≤ (∑ ω : Ω, f ω) / Fintype.card Ω := by
    rw [← dhj_average_density_rows_eq_columns E]
    exact hrows
  have hpoint : ∀ ω ∈ (Finset.univ : Finset Ω),
      f ω ≤ α / 2 + if ω ∈ B then 1 else 0 := by
    intro ω hω
    by_cases hωB : ω ∈ B
    · simp only [hωB, ↓reduceIte]
      have hf := dhjDensity_le_one (dhjColumn E ω)
      linarith
    · simp only [hωB, ↓reduceIte, add_zero]
      have : ¬α / 2 ≤ f ω := by
        simpa [B, dhjDenseColumns, f] using hωB
      exact le_of_lt (lt_of_not_ge this)
  have hsumUpper : (∑ ω : Ω, f ω) ≤
      Fintype.card Ω * (α / 2) + B.card := by
    calc
      (∑ ω : Ω, f ω) ≤ ∑ ω : Ω, (α / 2 + if ω ∈ B then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
      _ = Fintype.card Ω * (α / 2) + B.card := by
        rw [Finset.sum_add_distrib]
        simp
  have hsumLower : α * Fintype.card Ω ≤ ∑ ω : Ω, f ω := by
    rw [le_div_iff₀ (by positivity)] at havg
    simpa [mul_comm] using havg
  change α / 2 ≤ (B.card : ℝ) / Fintype.card Ω
  rw [le_div_iff₀ (by positivity)]
  nlinarith

private noncomputable def dhjInitialSubspace {α : Type*} [Nonempty α] {d m : ℕ}
    (h : d ≤ m) : Combinatorics.Subspace (Fin d) α (Fin m) where
  idxFun i := if hi : i.val < d then Sum.inr ⟨i.val, hi⟩
    else Sum.inl (Classical.choice ‹Nonempty α›)
  proper j := ⟨Fin.castLE h j, by simp⟩

private noncomputable def dhjLineEvent {α ι Ω : Type*}
    [Fintype α] [Fintype Ω] (E : (ι → α) → Finset Ω)
    (l : Combinatorics.Line α ι) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω => ∀ a, ω ∈ E (l a)

private theorem dhjLineEvent_mono {α ι Ω : Type*}
    [Fintype α] [Fintype Ω] {E : (ι → α) → Finset Ω}
    {l : Combinatorics.Line α ι} {C : Finset Ω}
    (hC : ∀ ω ∈ C, ∀ a, ω ∈ E (l a)) : C ⊆ dhjLineEvent E l := by
  classical
  intro ω hω
  simp only [dhjLineEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hC ω hω

private theorem dhj_exists_correlated_events {k m₀ m : ℕ}
    (hk : 0 < k) (hm₀ : 0 < m₀) (hm : m₀ ≤ m) {α : ℝ} (hα : 0 < α)
    (hDHJ : dhjAt k m₀ (α / 2)) :
    ∃ G : ℕ, 0 < G ∧ ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (E : (Fin G → Fin k) → Finset Ω),
      (∀ x, α ≤ dhjDensity (E x)) →
      ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin G),
        ∀ l : Combinatorics.Line (Fin k) (Fin m),
          α / (2 * dhjLineCount k m₀) ≤
            dhjDensity (dhjLineEvent E (V.compLine l)) := by
  classical
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let _ : Nonempty (Fin m₀) := ⟨⟨0, hm₀⟩⟩
  let _ : Fintype (Combinatorics.Line (Fin k) (Fin m₀)) := Fintype.ofFinite _
  obtain ⟨G, hGR⟩ :=
    Combinatorics.Subspace.exists_lines_mono_in_high_dimension_fin (Fin k) Bool m
  have hmpos : 0 < m := lt_of_lt_of_le hm₀ hm
  obtain ⟨V₀, z₀, hV₀⟩ := hGR fun _ => false
  obtain ⟨i, hi⟩ := V₀.proper ⟨0, hmpos⟩
  have hG : 0 < G := Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ i)
  refine ⟨G, hG, ?_⟩
  intro Ω instΩ nonemptyΩ E hE
  let good : Combinatorics.Line (Fin k) (Fin G) → Prop := fun l =>
    α / (2 * dhjLineCount k m₀) ≤ dhjDensity (dhjLineEvent E l)
  let color : Combinatorics.Line (Fin k) (Fin G) → Bool := fun l => decide (good l)
  obtain ⟨V, z, hV⟩ := hGR color
  let Q : Combinatorics.Subspace (Fin m₀) (Fin k) (Fin m) := dhjInitialSubspace hm
  let Z := V.comp Q
  let E' : (Fin m₀ → Fin k) → Finset Ω := fun x => E (Z x)
  have hE' : ∀ x, α ≤ dhjDensity (E' x) := fun x => hE (Z x)
  let B := dhjDenseColumns E' α
  have hB : α / 2 ≤ dhjDensity B := dhjDensity_denseColumns E' hα hE'
  have hLineAt (ω : Ω) (hω : ω ∈ B) :
      ∃ l : Combinatorics.Line (Fin k) (Fin m₀),
        ∀ a, ω ∈ E' (l a) := by
    have hcol : α / 2 ≤ dhjDensity (dhjColumn E' ω) :=
      (Finset.mem_filter.mp hω).2
    obtain ⟨l, hl⟩ := hDHJ (dhjColumn E' ω) hcol
    refine ⟨l, fun a => ?_⟩
    simpa [dhjColumn] using hl a
  let chosen : Ω → Combinatorics.Line (Fin k) (Fin m₀) := fun ω =>
    if hω : ω ∈ B then Classical.choose (hLineAt ω hω) else default
  have hchosen (ω : Ω) (hω : ω ∈ B) : ∀ a, ω ∈ E' (chosen ω a) := by
    simpa [chosen, hω] using Classical.choose_spec (hLineAt ω hω)
  obtain ⟨l₀, hl₀⟩ := dhj_exists_dense_fiber B chosen
  let C := B.filter fun ω => chosen ω = l₀
  have hcount : Fintype.card (Combinatorics.Line (Fin k) (Fin m₀)) =
      dhjLineCount k m₀ := by
    simp [dhjLineCount, Nat.card_eq_fintype_card]
  have hC : α / (2 * dhjLineCount k m₀) ≤ dhjDensity C := by
    calc
      α / (2 * dhjLineCount k m₀) =
          (α / 2) / Fintype.card (Combinatorics.Line (Fin k) (Fin m₀)) := by
        rw [hcount]
        field_simp
      _ ≤ dhjDensity B / Fintype.card (Combinatorics.Line (Fin k) (Fin m₀)) := by
        gcongr
      _ ≤ dhjDensity C := by simpa [C] using hl₀
  have hCsub : C ⊆ dhjLineEvent E (Z.compLine l₀) := by
    apply dhjLineEvent_mono
    intro ω hω a
    have hωB : ω ∈ B := (Finset.mem_filter.mp hω).1
    have hωline := hchosen ω hωB a
    have hωeq : chosen ω = l₀ := (Finset.mem_filter.mp hω).2
    rw [hωeq] at hωline
    simpa [E', Z, Combinatorics.Subspace.comp_compLine] using hωline
  have hgood : good (Z.compLine l₀) := by
    dsimp only [good]
    exact hC.trans (dhjDensity_mono hCsub)
  refine ⟨V, ?_⟩
  intro l
  have hsame : color (V.compLine l) = color (Z.compLine l₀) := by
    calc
      color (V.compLine l) = z := hV l
      _ = color (V.compLine (Q.compLine l₀)) := (hV (Q.compLine l₀)).symm
      _ = color (Z.compLine l₀) := by simp [Z, Combinatorics.Subspace.comp_compLine]
  have htrue : color (Z.compLine l₀) = true := by simp [color, hgood]
  have : color (V.compLine l) = true := hsame.trans htrue
  simpa [color, good] using this

private def dhjSubspaceMapConstants {η α β ι : Type*} (f : α → β)
    (V : Combinatorics.Subspace η α ι) : Combinatorics.Subspace η β ι where
  idxFun i := (V.idxFun i).map f id
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨i, by simp [hi]⟩

@[simp]
private theorem dhjSubspaceMapConstants_apply {η α β ι : Type*} (f : α → β)
    (V : Combinatorics.Subspace η α ι) (x : η → α) :
    dhjSubspaceMapConstants f V (f ∘ x) = f ∘ V x := by
  funext i
  cases hi : V.idxFun i <;>
    simp [dhjSubspaceMapConstants, Combinatorics.Subspace.coe_apply, hi]

private def dhjFixSuffixSubspace {η α ι κ : Type*}
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun
    | Sum.inl i => V.idxFun i
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

@[simp]
private theorem dhjFixSuffixSubspace_apply {η α ι κ : Type*}
    (V : Combinatorics.Subspace η α ι) (y : κ → α) (x : η → α) :
    dhjFixSuffixSubspace V y x = dhjConcat (V x) y := by
  funext q
  cases q with
  | inl i => rfl
  | inr j => simp [dhjFixSuffixSubspace, dhjConcat, Combinatorics.Subspace.coe_apply]

private def dhjBlockSplitEquiv {L t r : ℕ} (h : t ≤ L) :
    (Fin t × Fin r) ⊕ (Fin (L - t) × Fin r) ≃ Fin L × Fin r :=
  (Equiv.sumProdDistrib (Fin t) (Fin (L - t)) (Fin r)).symm.trans
    (Equiv.prodCongr (dhjFinSplit h) (Equiv.refl (Fin r)))

private def dhjFlattenBlocks {α : Type*} {L r : ℕ}
    (w : Fin L → Fin r → α) : Fin L × Fin r → α := fun q => w q.1 q.2

private def dhjBlockFullSubspace {η α : Type*} {L r t : ℕ}
    (p : Fin t → Fin r → α) (V : Combinatorics.Subspace η α (Fin r))
    (y : Fin (L - (t + 1)) → Fin r → α) (h : t + 1 ≤ L) :
    Combinatorics.Subspace η α (Fin L × Fin r) :=
  (dhjFixSuffixSubspace ((dhjBlockPrefixSubspace p).comp V) (dhjFlattenBlocks y)).reindex
    (Equiv.refl η) (Equiv.refl α) (dhjBlockSplitEquiv h)

@[simp]
private theorem dhjBlockFullSubspace_apply {η α : Type*} {L r t : ℕ}
    (p : Fin t → Fin r → α) (V : Combinatorics.Subspace η α (Fin r))
    (y : Fin (L - (t + 1)) → Fin r → α) (h : t + 1 ≤ L) (x : η → α) :
    dhjBlockFullSubspace p V y h x =
      dhjFlattenBlocks (dhjBlockJoin (dhjAppend p (V x)) y h) := by
  funext q
  obtain ⟨q, rfl⟩ := (dhjBlockSplitEquiv h).surjective q
  cases q with
  | inl q =>
      rcases q with ⟨b, j⟩
      simp [dhjBlockFullSubspace, dhjBlockSplitEquiv, dhjFlattenBlocks,
        dhjBlockJoin, dhjConcat]
  | inr q =>
      rcases q with ⟨b, j⟩
      simp [dhjBlockFullSubspace, dhjBlockSplitEquiv, dhjFlattenBlocks,
        dhjBlockJoin, dhjConcat]

private theorem dhj_lemma7_blocks {k m₀ m : ℕ}
    (hk : 0 < k) (hm₀ : 0 < m₀) (hm : m₀ ≤ m) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hεle : ε ≤ δ / 2)
    (hDHJ : dhjAt k m₀ (δ / 4)) :
    ∃ (G R : ℕ), 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → (Fin G → Fin (k + 1))),
        δ ≤ dhjDensity A →
        ∃ (t : ℕ) (ht : t ≤ R) (p : Fin t → Fin G → Fin (k + 1))
          (V : Combinatorics.Subspace (Fin m) (Fin k) (Fin G)),
          (∀ x : Fin m → Fin (k + 1),
            δ - ε ≤ dhjDensity (dhjBlockSection A
              (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega))) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin m),
            δ / (4 * dhjLineCount k m₀) ≤
              dhjDensity (dhjLineEvent
                (fun z => dhjBlockSection A
                  (dhjAppend p (Fin.castSucc ∘ V z)) (by omega)) l) := by
  classical
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let _ : Nonempty (Fin (k + 1)) := ⟨0⟩
  have hDHJ' : dhjAt k m₀ ((δ / 2) / 2) := by
    convert hDHJ using 1; ring
  obtain ⟨G, hG, hCorr⟩ :=
    dhj_exists_correlated_events hk hm₀ hm (show 0 < δ / 2 by positivity) hDHJ'
  let X := Fin G → Fin (k + 1)
  let _ : Nonempty X := inferInstance
  have hq : 2 ≤ Fintype.card X := by
    dsimp only [X]
    simp only [Fintype.card_fun, Fintype.card_fin]
    have hk2 : 2 ≤ k + 1 := by omega
    exact hk2.trans (Nat.le_pow hG)
  obtain ⟨R, hR⟩ := dhj_exists_regular_length hq hε
  refine ⟨G, R, hG, ?_⟩
  intro A hA
  obtain ⟨t, ht, p, hp⟩ := dhj_exists_regular_blockSection hq R A hε hR
  let E : (Fin G → Fin k) → Finset (Fin (R + 1 - (t + 1)) → X) := fun z =>
    dhjBlockSection A (dhjAppend p (Fin.castSucc ∘ z)) (by omega)
  have hE : ∀ z, δ / 2 ≤ dhjDensity (E z) := by
    intro z
    calc
      δ / 2 ≤ δ - ε := by linarith
      _ ≤ dhjDensity A - ε := sub_le_sub_right hA ε
      _ ≤ dhjDensity (E z) := hp (Fin.castSucc ∘ z)
  obtain ⟨V, hV⟩ := hCorr (Fin (R + 1 - (t + 1)) → X) E hE
  refine ⟨t, ht, p, V, ?_, ?_⟩
  · intro x
    exact (sub_le_sub_right hA ε).trans
      (hp (dhjSubspaceMapConstants Fin.castSucc V x))
  · intro l
    have hl := hV l
    have heq : dhjLineEvent E (V.compLine l) =
        dhjLineEvent (fun z => dhjBlockSection A
          (dhjAppend p (Fin.castSucc ∘ V z)) (by omega)) l := by
      ext y
      simp [dhjLineEvent, E, Function.comp_def]
    rw [heq] at hl
    convert hl using 1; ring

private noncomputable def dhjSuperlevel {Y : Type*} [Fintype Y]
    (f : Y → ℝ) (c : ℝ) : Finset Y := by
  classical
  exact Finset.univ.filter fun y => c ≤ f y

private theorem dhj_concentration_from_narrow_average {Y : Type*}
    [Fintype Y] [Nonempty Y] (f : Y → ℝ) {δ η : ℝ} (hη : 0 < η)
    (havg : δ - η ^ 2 / 2 ≤ Finset.expect Finset.univ f)
    (hupper : ∀ y, f y < δ + η ^ 2 / 2) :
    1 - η ≤ dhjDensity (dhjSuperlevel f (δ - 2 * η)) := by
  classical
  let H := dhjSuperlevel f (δ - 2 * η)
  have hpoint : ∀ y ∈ (Finset.univ : Finset Y),
      f y ≤ if y ∈ H then δ + η ^ 2 / 2 else δ - 2 * η := by
    intro y hy
    by_cases hyH : y ∈ H
    · simp only [hyH, ↓reduceIte]
      exact (hupper y).le
    · simp only [hyH, ↓reduceIte]
      have : ¬δ - 2 * η ≤ f y := by
        simpa [H, dhjSuperlevel] using hyH
      exact le_of_lt (lt_of_not_ge this)
  have hsumUpper : (∑ y : Y, f y) ≤
      H.card * (δ + η ^ 2 / 2) +
        (Fintype.card Y - H.card) * (δ - 2 * η) := by
    calc
      (∑ y : Y, f y) ≤
          ∑ y : Y, (if y ∈ H then δ + η ^ 2 / 2 else δ - 2 * η) :=
        Finset.sum_le_sum hpoint
      _ = H.card * (δ + η ^ 2 / 2) +
          (Fintype.card Y - H.card) * (δ - 2 * η) := by
        rw [Finset.sum_ite]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.filter_notMem_eq_sdiff]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.card_sdiff_of_subset H.subset_univ, Finset.card_univ,
          Nat.cast_sub H.card_le_univ]
  have hsumLower : (δ - η ^ 2 / 2) * Fintype.card Y ≤ ∑ y : Y, f y := by
    rw [Fintype.expect_eq_sum_div_card, le_div_iff₀ (by positivity)] at havg
    simpa [mul_comm] using havg
  by_contra hH
  have hHlt : (H.card : ℝ) / Fintype.card Y < 1 - η := by
    have hH' : ¬1 - η ≤ (H.card : ℝ) / Fintype.card Y := by
      change ¬1 - η ≤ (H.card : ℝ) / Fintype.card Y at hH
      exact hH
    exact lt_of_not_ge hH'
  have hq : (0 : ℝ) < Fintype.card Y := by positivity
  have hcard : H.card ≤ Fintype.card Y := H.card_le_univ
  rw [div_lt_iff₀ hq] at hHlt
  have hcpos : 0 < η ^ 2 / 2 + 2 * η := by nlinarith [sq_nonneg η]
  have hweighted := mul_lt_mul_of_pos_right hHlt hcpos
  nlinarith [sq_pos_of_pos hη, mul_pos hq (sq_pos_of_pos hη)]

private theorem dhj_inter_nonempty_of_density {Y : Type*} [Fintype Y] [Nonempty Y]
    {A B : Finset Y} {a b : ℝ} (hA : a ≤ dhjDensity A) (hB : b ≤ dhjDensity B)
    (hab : 1 < a + b) : ∃ y, y ∈ A ∧ y ∈ B := by
  classical
  by_contra hne
  push Not at hne
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun y hyA hyB => hne y hyA hyB
  have hcard : A.card + B.card ≤ Fintype.card Y := by
    rw [← Finset.card_disjUnion A B hdisj]
    exact (A.disjUnion B hdisj).card_le_univ
  have hdens : dhjDensity A + dhjDensity B ≤ 1 := by
    simp only [dhjDensity, ← add_div, ← Nat.cast_add]
    rw [div_le_one (by positivity)]
    exact_mod_cast hcard
  linarith

private theorem dhj_lemma8_blocks {k m G R t : ℕ} {δ η θ : ℝ}
    (hk : 0 < k) (hm : 0 < m) (hη : 0 < η) (hθ : 0 < θ) (hηθ : η < θ / 2)
    (ht : t ≤ R) (A : Finset (Fin (R + 1) → (Fin G → Fin (k + 1))))
    (p : Fin t → Fin G → Fin (k + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin k) (Fin G))
    (hsections : ∀ x : Fin m → Fin (k + 1),
      δ - η ^ 2 / 2 ≤ dhjDensity (dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ dhjDensity (dhjLineEvent
        (fun z => dhjBlockSection A (dhjAppend p (Fin.castSucc ∘ V z)) (by omega)) l)) :
    (∃ y : Fin (R + 1 - (t + 1)) → (Fin G → Fin (k + 1)),
      δ + η ^ 2 / 2 ≤ dhjDensity (dhjColumn
        (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
          (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y)) ∨
    ∃ y : Fin (R + 1 - (t + 1)) → (Fin G → Fin (k + 1)),
      δ - 2 * η ≤ dhjDensity (dhjColumn
        (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
          (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y) ∧
      θ / 2 ≤ dhjDensity (dhjColumn
        (fun l : Combinatorics.Line (Fin k) (Fin m) => dhjLineEvent
          (fun z => dhjBlockSection A (dhjAppend p (Fin.castSucc ∘ V z)) (by omega)) l) y) := by
  classical
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let X := Fin m → Fin (k + 1)
  let Y := Fin (R + 1 - (t + 1)) → (Fin G → Fin (k + 1))
  let Epoint : X → Finset Y := fun x => dhjBlockSection A
    (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)
  let Eline : Combinatorics.Line (Fin k) (Fin m) → Finset Y := fun l =>
    dhjLineEvent (fun z => dhjBlockSection A
      (dhjAppend p (Fin.castSucc ∘ V z)) (by omega)) l
  let f : Y → ℝ := fun y => dhjDensity (dhjColumn Epoint y)
  have havg : δ - η ^ 2 / 2 ≤ Finset.expect Finset.univ f := by
    rw [Fintype.expect_eq_sum_div_card]
    rw [← dhj_average_density_rows_eq_columns Epoint]
    rw [le_div_iff₀ (by positivity)]
    have hs := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset X)) => hsections x
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    rw [Finset.card_univ] at hs
    dsimp only [Epoint, X] at hs ⊢
    nlinarith
  by_cases hinc : ∃ y : Y, δ + η ^ 2 / 2 ≤ f y
  · exact Or.inl hinc
  right
  have hupper : ∀ y : Y, f y < δ + η ^ 2 / 2 := by
    intro y
    exact lt_of_not_ge fun hy => hinc ⟨y, hy⟩
  let H₁ := dhjSuperlevel f (δ - 2 * η)
  have hH₁ : 1 - η ≤ dhjDensity H₁ :=
    dhj_concentration_from_narrow_average f hη havg hupper
  let H₂ := dhjDenseColumns Eline θ
  have hH₂ : θ / 2 ≤ dhjDensity H₂ := dhjDensity_denseColumns Eline hθ hlines
  obtain ⟨y, hy₁, hy₂⟩ := dhj_inter_nonempty_of_density hH₁ hH₂ (by linarith)
  refine ⟨y, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hy₁).2
  · exact (Finset.mem_filter.mp hy₂).2

private def dhjDropLast {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) : ι → Fin k := fun q => Fin.lastCases i id (x q)

private def dhjReplaceLast {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) : ι → Fin (k + 1) :=
  Fin.castSucc ∘ dhjDropLast i x

@[simp]
private theorem dhjDropLast_castSucc {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin k) : dhjDropLast i (Fin.castSucc ∘ x) = x := by
  funext q
  simp [dhjDropLast]

@[simp]
private theorem dhjReplaceLast_castSucc {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin k) : dhjReplaceLast i (Fin.castSucc ∘ x) = Fin.castSucc ∘ x := by
  simp [dhjReplaceLast]

@[simp]
private theorem dhjReplaceLast_idem {k : ℕ} {ι : Type*} (i : Fin k)
    (x : ι → Fin (k + 1)) :
    dhjReplaceLast i (dhjReplaceLast i x) = dhjReplaceLast i x := by
  simp [dhjReplaceLast]

@[simp]
private theorem dhjReplaceLast_lineTop {k : ℕ} {ι : Type*}
    (i : Fin k) (l : Combinatorics.Line (Fin k) ι) :
    dhjReplaceLast i (dhjLineTop l) = Fin.castSucc ∘ l i := by
  funext q
  cases hq : l.idxFun q <;>
    simp [dhjReplaceLast, dhjDropLast, dhjLineTop, dhjLiftLine,
      Combinatorics.Line.coe_apply, hq]

private def dhjInsensitive {k : ℕ} {ι : Type*} (i : Fin k)
    (D : Finset (ι → Fin (k + 1))) : Prop :=
  ∀ x, x ∈ D ↔ dhjReplaceLast i x ∈ D

private noncomputable def dhjInsensitivePreimage {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => dhjReplaceLast i x ∈ B

private theorem dhjInsensitive_preimage {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    dhjInsensitive i (dhjInsensitivePreimage B i) := by
  classical
  intro x
  simp [dhjInsensitivePreimage]

private noncomputable def dhjCore {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ i : Fin k, dhjReplaceLast i x ∈ B

@[simp]
private theorem dhj_mem_core {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) :
    x ∈ dhjCore B ↔ ∀ i : Fin k, dhjReplaceLast i x ∈ B := by
  classical
  simp [dhjCore]

private theorem dhj_mem_core_iff_preimages {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) :
    x ∈ dhjCore B ↔ ∀ i : Fin k, x ∈ dhjInsensitivePreimage B i := by
  classical
  simp [dhjInsensitivePreimage]

private noncomputable def dhjGoodRestrictedLines {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1))) :
    Finset (Combinatorics.Line (Fin k) ι) := by
  classical
  exact Finset.univ.filter fun l => ∀ a : Fin k, Fin.castSucc ∘ l a ∈ B

@[simp]
private theorem dhj_mem_goodRestrictedLines {k : ℕ} {ι : Type*}
    [Fintype ι] (B : Finset (ι → Fin (k + 1)))
    (l : Combinatorics.Line (Fin k) ι) :
    l ∈ dhjGoodRestrictedLines B ↔ ∀ a : Fin k, Fin.castSucc ∘ l a ∈ B := by
  classical
  simp [dhjGoodRestrictedLines]

private theorem dhjLineTop_injective {k : ℕ} {ι : Type*} :
    Function.Injective (dhjLineTop : Combinatorics.Line (Fin k) ι → ι → Fin (k + 1)) := by
  intro l l' h
  rw [← dhjLineOfTop_lineTop l, ← dhjLineOfTop_lineTop l']
  congr

private theorem dhj_goodLines_card_le_core {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) :
    (dhjGoodRestrictedLines B).card ≤ (dhjCore B).card := by
  classical
  apply Finset.card_le_card_of_injOn dhjLineTop
  · intro l hl
    change dhjLineTop l ∈ dhjCore B
    rw [dhj_mem_core]
    intro i
    rw [dhjReplaceLast_lineTop]
    exact (dhj_mem_goodRestrictedLines B l).mp hl i
  · exact dhjLineTop_injective.injOn

private theorem dhj_core_density_lower {k m : ℕ} {θ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hθ : 0 ≤ θ)
    (B : Finset (Fin m → Fin (k + 1)))
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    θ / 4 ≤ dhjDensity (dhjCore B) := by
  have hmpos : 0 < m := lt_of_lt_of_le hk hm
  have hlinepos : (0 : ℝ) < dhjLineCount k m := by
    exact_mod_cast dhjLineCount_pos hmpos
  have hcount : Fintype.card (Combinatorics.Line (Fin k) (Fin m)) =
      dhjLineCount k m := by
    simp [dhjLineCount, Nat.card_eq_fintype_card]
  rw [dhjDensity, hcount, le_div_iff₀ hlinepos] at hgood
  rw [dhjDensity]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [le_div_iff₀ (by positivity)]
  have hcard := dhj_goodLines_card_le_core B
  have hhalf := dhj_half_cube_le_lineCount hk hm
  have hcardR : ((dhjGoodRestrictedLines B).card : ℝ) ≤ (dhjCore B).card := by
    exact_mod_cast hcard
  have hhalfR : ((k + 1 : ℕ) ^ m : ℝ) ≤ 2 * dhjLineCount k m := by
    exact_mod_cast hhalf
  nlinarith

private theorem dhj_lineFree_inter_core_noLast {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B) :
    ∀ x ∈ B ∩ dhjCore B, ∀ q, x q ≠ Fin.last k := by
  classical
  intro x hx q hxq
  have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
  have hxC : x ∈ dhjCore B := (Finset.mem_inter.mp hx).2
  have hxlast : dhjHasLast x := by
    rw [dhjHasLast]
    intro h
    exact h q hxq
  let l := dhjLineOfTop x hxlast
  apply hB (dhjLiftLine l)
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have htop : dhjLineTop l = x := dhjLineTop_lineOfTop x hxlast
    change dhjLineTop l ∈ B
    rw [htop]
    exact hxB
  · rw [dhjLiftLine_apply]
    have hreplace : dhjReplaceLast i x = Fin.castSucc ∘ l i := by
      rw [← dhjLineTop_lineOfTop x hxlast]
      exact dhjReplaceLast_lineTop i l
    rw [← hreplace]
    exact (dhj_mem_core B x).mp hxC i

private theorem dhj_inter_core_density_le_ratio {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B) :
    dhjDensity (B ∩ dhjCore B) ≤ ((k : ℝ) / (k + 1)) ^ m := by
  classical
  let S : Finset (Fin m → Fin (k + 1)) :=
    Finset.univ.filter fun x => ∀ q, x q ≠ Fin.last k
  have hsub : B ∩ dhjCore B ⊆ S := by
    intro x hx
    simpa [S] using dhj_lineFree_inter_core_noLast B hB x hx
  apply (dhjDensity_mono hsub).trans_eq
  rw [dhjDensity]
  have hcardS : S.card = k ^ m := by
    rw [show S.card = Fintype.card {x : Fin m → Fin (k + 1) //
        ∀ q, x q ≠ Fin.last k} by
      rw [Fintype.card_subtype]]
    rw [Fintype.card_congr (dhjNoLastEquiv (k := k) (ι := Fin m))]
    simp
  rw [hcardS]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_pow]
  norm_num

private theorem dhj_density_inter_add_sdiff {X : Type*} [Fintype X]
    [DecidableEq X] (A C : Finset X) :
    dhjDensity (A ∩ C) + dhjDensity (A \ C) = dhjDensity A := by
  simp only [dhjDensity, ← add_div, ← Nat.cast_add]
  rw [Finset.card_inter_add_card_sdiff]

private theorem dhj_density_compl {X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq X] (C : Finset X) :
    dhjDensity (Finset.univ \ C) = 1 - dhjDensity C := by
  have h := dhjDensity_sdiff_add (A := (Finset.univ : Finset X)) C.subset_univ
  rw [dhjDensity_univ] at h
  linarith

private theorem dhj_lemma10_cube {k m : ℕ} {δ η θ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hδ : 0 < δ) (hθ : 0 ≤ θ)
    (hη : η = δ * θ / 48)
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ η)
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B)
    (hden : δ - 2 * η ≤ dhjDensity B)
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    let C := dhjCore B
    θ / 4 ≤ dhjDensity C ∧
      (∀ i : Fin k, dhjInsensitive i (dhjInsensitivePreimage B i)) ∧
      (∀ x, x ∈ C ↔ ∀ i : Fin k, x ∈ dhjInsensitivePreimage B i) ∧
      δ - 3 * η ≤ dhjDensity (B \ C) ∧
      (δ + 6 * η) * dhjDensity (Finset.univ \ C) ≤ dhjDensity (B \ C) := by
  classical
  dsimp only
  have hC : θ / 4 ≤ dhjDensity (dhjCore B) :=
    dhj_core_density_lower hk hm hθ B hgood
  have hBC : dhjDensity (B ∩ dhjCore B) ≤ η :=
    (dhj_inter_core_density_le_ratio B hB).trans hratio
  have hpartition := dhj_density_inter_add_sdiff B (dhjCore B)
  have hdiff : δ - 3 * η ≤ dhjDensity (B \ dhjCore B) := by
    linarith
  have hcomp : dhjDensity (Finset.univ \ dhjCore B) =
      1 - dhjDensity (dhjCore B) := dhj_density_compl (dhjCore B)
  have hcompUpper : dhjDensity (Finset.univ \ dhjCore B) ≤ 1 - θ / 4 := by
    rw [hcomp]
    linarith
  have hηnonneg : 0 ≤ η := by rw [hη]; positivity
  have hcoef : 0 ≤ δ + 6 * η := by positivity
  have hnumeric : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η := by
    rw [hη]
    nlinarith [mul_nonneg hδ.le (sq_nonneg θ)]
  refine ⟨hC, fun i => dhjInsensitive_preimage B i,
    fun x => dhj_mem_core_iff_preimages B x, hdiff, ?_⟩
  calc
    (δ + 6 * η) * dhjDensity (Finset.univ \ dhjCore B) ≤
        (δ + 6 * η) * (1 - θ / 4) := mul_le_mul_of_nonneg_left hcompUpper hcoef
    _ ≤ δ - 3 * η := hnumeric
    _ ≤ dhjDensity (B \ dhjCore B) := hdiff

private theorem dhj_exists_ratio_pow_le {k : ℕ} (hk : 0 < k) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, k ≤ M ∧ ∀ m ≥ M, ((k : ℝ) / (k + 1)) ^ m ≤ η := by
  have hrpos : 0 < (k : ℝ) / (k + 1) := by positivity
  have hrlt : (k : ℝ) / (k + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    norm_num
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη hrlt
  refine ⟨max k n, le_max_left _ _, ?_⟩
  intro m hm
  have hnm : n ≤ m := (le_max_right k n).trans hm
  exact (pow_le_pow_of_le_one hrpos.le hrlt.le hnm).trans hn.le

private noncomputable def dhjFiber {X I : Type*} [Fintype X]
    (Q : Finset X) (f : X → I) (i : I) : Finset X := by
  classical
  exact Q.filter fun x => f x = i

@[simp]
private theorem dhj_mem_fiber {X I : Type*} [Fintype X]
    (Q : Finset X) (f : X → I) (i : I) (x : X) :
    x ∈ dhjFiber Q f i ↔ x ∈ Q ∧ f x = i := by
  classical
  simp [dhjFiber]

private theorem dhj_sum_density_fibers {X I : Type*} [Fintype X] [Fintype I]
    (Q : Finset X) (f : X → I) :
    (∑ i : I, dhjDensity (dhjFiber Q f i)) = dhjDensity Q := by
  classical
  have hcard : Q.card = ∑ i : I, (dhjFiber Q f i).card := by
    apply Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    intro x hx
    simp
  simp only [dhjDensity, ← Finset.sum_div, ← Nat.cast_sum]
  rw [← hcard]

private theorem dhj_inter_fiber {X I : Type*} [Fintype X] [DecidableEq X]
    (A Q : Finset X) (f : X → I) (i : I) :
    A ∩ dhjFiber Q f i = dhjFiber (A ∩ Q) f i := by
  classical
  ext x
  simp [dhjFiber, and_assoc]

private theorem dhj_sum_density_inter_fibers {X I : Type*} [Fintype X] [DecidableEq X]
    [Fintype I]
    (A Q : Finset X) (f : X → I) :
    (∑ i : I, dhjDensity (A ∩ dhjFiber Q f i)) = dhjDensity (A ∩ Q) := by
  simp_rw [dhj_inter_fiber]
  exact dhj_sum_density_fibers (A ∩ Q) f

private theorem dhj_exists_large_correlated_fiber {X : Type*} [Fintype X] [DecidableEq X]
    {k : ℕ} (hk : 0 < k) (A Q : Finset X) (f : X → Fin k)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hQ : 0 < dhjDensity Q)
    (hcorr : (δ + 6 * η) * dhjDensity Q ≤ dhjDensity (A ∩ Q)) :
    ∃ i : Fin k,
      (3 * η / k) * dhjDensity Q ≤ dhjDensity (dhjFiber Q f i) ∧
        (δ + 3 * η) * dhjDensity (dhjFiber Q f i) ≤
          dhjDensity (A ∩ dhjFiber Q f i) := by
  classical
  let w : Fin k → ℝ := fun i => dhjDensity (dhjFiber Q f i)
  let a : Fin k → ℝ := fun i => dhjDensity (A ∩ dhjFiber Q f i)
  let c : ℝ := δ + 3 * η
  let τ : ℝ := (3 * η / k) * dhjDensity Q
  have hsumw : (∑ i : Fin k, w i) = dhjDensity Q :=
    dhj_sum_density_fibers Q f
  have hsuma : (∑ i : Fin k, a i) = dhjDensity (A ∩ Q) :=
    dhj_sum_density_inter_fibers A Q f
  have ha_le_w : ∀ i, a i ≤ w i := by
    intro i
    exact dhjDensity_mono Finset.inter_subset_right
  have hAQle : dhjDensity (A ∩ Q) ≤ dhjDensity Q :=
    dhjDensity_mono Finset.inter_subset_right
  have hc_le_one : c ≤ 1 := by
    dsimp only [c]
    have : (δ + 6 * η) * dhjDensity Q ≤ dhjDensity Q := hcorr.trans hAQle
    nlinarith
  have hc_nonneg : 0 ≤ c := by dsimp only [c]; positivity
  have hτnonneg : 0 ≤ τ := by dsimp only [τ]; positivity
  by_contra hex
  push Not at hex
  let H : Finset (Fin k) := Finset.univ.filter fun i => c * w i ≤ a i
  have hsmall : ∀ i ∈ H, w i ≤ τ := by
    intro i hi
    have hiH : c * w i ≤ a i := (Finset.mem_filter.mp hi).2
    by_contra hwi
    have hlarge : τ ≤ w i := le_of_not_ge hwi
    exact (not_lt_of_ge hiH) (hex i hlarge)
  have hsumH : (∑ i ∈ H, w i) ≤ 3 * η * dhjDensity Q := by
    calc
      (∑ i ∈ H, w i) ≤ H.card * τ :=
        by simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul H w τ hsmall
      _ ≤ k * τ := by
        gcongr
        simpa using H.card_le_univ
      _ = 3 * η * dhjDensity Q := by
        dsimp only [τ]
        field_simp
  have hpoint : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      a i ≤ c * w i + if i ∈ H then (1 - c) * w i else 0 := by
    intro i hi
    by_cases hiH : i ∈ H
    · simp only [hiH, ↓reduceIte]
      have hai := ha_le_w i
      nlinarith
    · simp only [hiH, ↓reduceIte, add_zero]
      exact (lt_of_not_ge (by simpa [H] using hiH)).le
  have hsumUpper : (∑ i : Fin k, a i) ≤
      c * (∑ i : Fin k, w i) + (1 - c) * ∑ i ∈ H, w i := by
    calc
      (∑ i : Fin k, a i) ≤
          ∑ i : Fin k, (c * w i + if i ∈ H then (1 - c) * w i else 0) :=
        Finset.sum_le_sum hpoint
      _ = c * (∑ i : Fin k, w i) + (1 - c) * ∑ i ∈ H, w i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_ite_mem]
        rw [Finset.univ_inter]
        rw [Finset.mul_sum]
  have hupper : dhjDensity (A ∩ Q) ≤
      c * dhjDensity Q + (1 - c) * (3 * η * dhjDensity Q) := by
    rw [hsuma, hsumw] at hsumUpper
    apply hsumUpper.trans
    gcongr
  have hstrict : c * dhjDensity Q + (1 - c) * (3 * η * dhjDensity Q) <
      (δ + 6 * η) * dhjDensity Q := by
    have hpos : 0 < 3 * η * c * dhjDensity Q := by positivity
    dsimp only [c]
    calc
      (δ + 3 * η) * dhjDensity Q +
          (1 - (δ + 3 * η)) * (3 * η * dhjDensity Q) =
          (δ + 6 * η) * dhjDensity Q -
            3 * η * (δ + 3 * η) * dhjDensity Q := by ring
      _ < (δ + 6 * η) * dhjDensity Q := sub_lt_self _ hpos
  exact (not_lt_of_ge (hcorr.trans hupper)) hstrict

private noncomputable def dhjBadIndices {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => x ∉ dhjInsensitivePreimage B i

private noncomputable def dhjFirstBad {k : ℕ} {ι : Type*} [Fintype ι]
    (i₀ : Fin k) (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) : Fin k :=
  if h : (dhjBadIndices B x).Nonempty then (dhjBadIndices B x).min' h else i₀

private theorem dhj_badIndices_nonempty_of_not_core {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1))
    (hx : x ∉ dhjCore B) : (dhjBadIndices B x).Nonempty := by
  classical
  have hnot : ¬∀ i : Fin k, x ∈ dhjInsensitivePreimage B i := by
    intro h
    exact hx ((dhj_mem_core_iff_preimages B x).mpr h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  exact ⟨i, by simp [dhjBadIndices, hi]⟩

private theorem dhj_firstBad_not_mem {k : ℕ} {ι : Type*} [Fintype ι]
    (i₀ : Fin k) (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1))
    (hx : x ∉ dhjCore B) :
    x ∉ dhjInsensitivePreimage B (dhjFirstBad i₀ B x) := by
  classical
  have hne := dhj_badIndices_nonempty_of_not_core B x hx
  rw [dhjFirstBad, dite_eq_left hne]
  have hmem := Finset.min'_mem (dhjBadIndices B x) hne
  exact (Finset.mem_filter.mp hmem).2

private theorem dhj_mem_before_firstBad {k : ℕ} {ι : Type*} [Fintype ι]
    (i₀ : Fin k) (B : Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1))
    (hx : x ∉ dhjCore B) {j : Fin k} (hj : j < dhjFirstBad i₀ B x) :
    x ∈ dhjInsensitivePreimage B j := by
  classical
  have hne := dhj_badIndices_nonempty_of_not_core B x hx
  rw [dhjFirstBad, dite_eq_left hne] at hj
  by_contra hjmem
  have hjbad : j ∈ dhjBadIndices B x := by simp [dhjBadIndices, hjmem]
  exact hj.not_ge (Finset.min'_le _ _ hjbad)

private noncomputable def dhjCell {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (i : Fin k) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x =>
    x ∉ dhjInsensitivePreimage B i ∧
      ∀ j : Fin k, j < i → x ∈ dhjInsensitivePreimage B j

@[simp]
private theorem dhj_mem_cell {k : ℕ} {ι : Type*} [Fintype ι]
    (B : Finset (ι → Fin (k + 1))) (i : Fin k) (x : ι → Fin (k + 1)) :
    x ∈ dhjCell B i ↔ x ∉ dhjInsensitivePreimage B i ∧
      ∀ j : Fin k, j < i → x ∈ dhjInsensitivePreimage B j := by
  classical
  simp [dhjCell]

private theorem dhj_cell_subset_compl_core {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))]
    (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    dhjCell B i ⊆ Finset.univ \ dhjCore B := by
  classical
  intro x hx
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hxC
  exact (dhj_mem_cell B i x).mp hx |>.1
    ((dhj_mem_core_iff_preimages B x).mp hxC i)

private theorem dhj_fiber_firstBad_eq_cell {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))]
    (i₀ : Fin k) (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    dhjFiber (Finset.univ \ dhjCore B) (dhjFirstBad i₀ B) i = dhjCell B i := by
  classical
  ext x
  constructor
  · intro hx
    have hx' := (dhj_mem_fiber _ _ _ _).mp hx
    have hxQ := Finset.mem_sdiff.mp hx'.1
    rw [dhj_mem_cell]
    constructor
    · rw [← hx'.2]
      exact dhj_firstBad_not_mem i₀ B x hxQ.2
    · intro j hj
      rw [← hx'.2] at hj
      exact dhj_mem_before_firstBad i₀ B x hxQ.2 hj
  · intro hx
    have hxcell := (dhj_mem_cell B i x).mp hx
    have hxQ : x ∈ Finset.univ \ dhjCore B := dhj_cell_subset_compl_core B i hx
    rw [dhj_mem_fiber]
    refine ⟨hxQ, ?_⟩
    have hne := dhj_badIndices_nonempty_of_not_core B x (Finset.mem_sdiff.mp hxQ).2
    rw [dhjFirstBad, dite_eq_left hne]
    apply (Finset.min'_eq_iff _ _ i).mpr
    constructor
    · simp [dhjBadIndices, hxcell.1]
    · intro j hjbad
      have hjnot : x ∉ dhjInsensitivePreimage B j :=
        (Finset.mem_filter.mp hjbad).2
      exact le_of_not_gt fun hji => hjnot (hxcell.2 j hji)

private theorem dhjInsensitive_compl {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] (i : Fin k) (D : Finset (ι → Fin (k + 1)))
    (hD : dhjInsensitive i D) : dhjInsensitive i (Finset.univ \ D) := by
  classical
  intro x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [hD x]

private theorem dhjInsensitive_univ {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] (i : Fin k) :
    dhjInsensitive i (Finset.univ : Finset (ι → Fin (k + 1))) := by
  intro x
  simp

private noncomputable def dhjCellFactor {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] (B : Finset (ι → Fin (k + 1)))
    (i j : Fin k) : Finset (ι → Fin (k + 1)) :=
  if j < i then dhjInsensitivePreimage B j
  else if j = i then Finset.univ \ dhjInsensitivePreimage B j
  else Finset.univ

private theorem dhj_cellFactor_insensitive {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] (B : Finset (ι → Fin (k + 1)))
    (i j : Fin k) : dhjInsensitive j (dhjCellFactor B i j) := by
  classical
  by_cases hji : j < i
  · simpa [dhjCellFactor, hji] using dhjInsensitive_preimage B j
  · by_cases hji' : j = i
    · simpa [dhjCellFactor, hji, hji'] using
        dhjInsensitive_compl j (dhjInsensitivePreimage B j) (dhjInsensitive_preimage B j)
    · simpa [dhjCellFactor, hji, hji'] using
        (dhjInsensitive_univ j :
          dhjInsensitive j (Finset.univ : Finset (ι → Fin (k + 1))))

private noncomputable def dhjFamilyMeet {k : ℕ} {ι : Type*} [Fintype ι]
    (D : Fin k → Finset (ι → Fin (k + 1))) : Finset (ι → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ i, x ∈ D i

@[simp]
private theorem dhj_mem_familyMeet {k : ℕ} {ι : Type*} [Fintype ι]
    (D : Fin k → Finset (ι → Fin (k + 1))) (x : ι → Fin (k + 1)) :
    x ∈ dhjFamilyMeet D ↔ ∀ i, x ∈ D i := by
  classical
  simp [dhjFamilyMeet]

private theorem dhj_familyMeet_cellFactor {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] (B : Finset (ι → Fin (k + 1))) (i : Fin k) :
    dhjFamilyMeet (dhjCellFactor B i) = dhjCell B i := by
  classical
  ext x
  rw [dhj_mem_familyMeet, dhj_mem_cell]
  constructor
  · intro hx
    constructor
    · have hi := hx i
      simpa [dhjCellFactor] using hi
    · intro j hj
      have hjmem := hx j
      simpa [dhjCellFactor, hj, ne_of_lt hj] using hjmem
  · rintro ⟨hxi, hbefore⟩ j
    by_cases hj : j < i
    · simpa [dhjCellFactor, hj] using hbefore j hj
    · by_cases hji : j = i
      · subst j
        simpa [dhjCellFactor] using hxi
      · simp [dhjCellFactor, hj, hji]

private theorem dhj_corollary11_cube {k m : ℕ} {δ η θ γ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hθ : 0 < θ) (hθle : θ ≤ 1) (hη : η = δ * θ / 48)
    (hγ : γ = δ * η ^ 2 / k)
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ η)
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B)
    (hden : δ - 2 * η ≤ dhjDensity B)
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, dhjInsensitive i (D i)) ∧
        γ ≤ dhjDensity (dhjFamilyMeet D) ∧
        (δ + γ) * dhjDensity (dhjFamilyMeet D) ≤
          dhjDensity (B ∩ dhjFamilyMeet D) := by
  classical
  obtain ⟨hC, hCi, hCeq, hdiff, hcorr⟩ :=
    dhj_lemma10_cube hk hm hδ hθ.le hη hratio B hB hden hgood
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηle : η ≤ δ / 48 := by
    rw [hη]
    gcongr
    exact mul_le_of_le_one_right hδ.le hθle
  have hδ3η : 0 < δ - 3 * η := by
    nlinarith
  let Q : Finset (Fin m → Fin (k + 1)) := Finset.univ \ dhjCore B
  have hBQ : B ∩ Q = B \ dhjCore B := by
    ext x
    simp [Q]
  have hBQsub : B \ dhjCore B ⊆ Q := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hQlower : δ - 3 * η ≤ dhjDensity Q :=
    hdiff.trans (dhjDensity_mono hBQsub)
  have hQpos : 0 < dhjDensity Q := hδ3η.trans_le hQlower
  let i₀ : Fin k := ⟨0, hk⟩
  obtain ⟨i, hiMass, hiCorr⟩ := dhj_exists_large_correlated_fiber hk B Q
    (dhjFirstBad i₀ B) hδ hηpos hQpos (by simpa [hBQ] using hcorr)
  have hfiber : dhjFiber Q (dhjFirstBad i₀ B) i = dhjCell B i := by
    exact dhj_fiber_firstBad_eq_cell i₀ B i
  rw [hfiber] at hiMass hiCorr
  let D := dhjCellFactor B i
  have hmeet : dhjFamilyMeet D = dhjCell B i := dhj_familyMeet_cellFactor B i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hηone : η ≤ 1 := hηle.trans (by linarith)
  have hγle3η : γ ≤ 3 * η := by
    rw [hγ]
    rw [div_le_iff₀ hkR]
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg hδ.le (sq_nonneg η)]
  have hγmass : γ ≤ dhjDensity (dhjCell B i) := by
    have hnum : δ * η ^ 2 ≤ 3 * η * (δ - 3 * η) := by
      nlinarith [mul_nonneg hδ.le (sq_nonneg η)]
    calc
      γ = δ * η ^ 2 / k := hγ
      _ ≤ (3 * η * (δ - 3 * η)) / k :=
        (div_le_div_iff_of_pos_right hkR).mpr hnum
      _ = (3 * η / k) * (δ - 3 * η) := by ring
      _ ≤ (3 * η / k) * dhjDensity Q := by gcongr
      _ ≤ dhjDensity (dhjCell B i) := hiMass
  refine ⟨D, fun j => dhj_cellFactor_insensitive B i j, ?_, ?_⟩
  · rwa [hmeet]
  · rw [hmeet]
    calc
      (δ + γ) * dhjDensity (dhjCell B i) ≤
          (δ + 3 * η) * dhjDensity (dhjCell B i) := by
        gcongr
        exact dhjDensity_nonneg _
      _ ≤ dhjDensity (B ∩ dhjCell B i) := hiCorr

private def dhjFlattenEquiv {L G : ℕ} {α : Type*} :
    (Fin L → Fin G → α) ≃ (Fin L × Fin G → α) where
  toFun := dhjFlattenBlocks
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem dhjPullback_blockFullSubspace {η α : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)] {L G t : ℕ}
    (A : Finset (Fin L → Fin G → α)) (p : Fin t → Fin G → α)
    (V : Combinatorics.Subspace η α (Fin G))
    (y : Fin (L - (t + 1)) → Fin G → α) (h : t + 1 ≤ L) :
    dhjPullback (dhjBlockFullSubspace p V y h)
        (A.map (dhjFlattenEquiv (L := L) (G := G) (α := α)).toEmbedding) =
      dhjColumn (fun x : η → α =>
        dhjBlockSection A (dhjAppend p (V x)) h) y := by
  classical
  ext x
  simp only [dhj_mem_pullback, dhjColumn, Finset.mem_filter, Finset.mem_univ, true_and,
    dhjBlockSection]
  rw [Finset.mem_map]
  constructor
  · rintro ⟨w, hw, hweq⟩
    have hwEq : w = dhjBlockJoin (dhjAppend p (V x)) y h := by
      apply (dhjFlattenEquiv (L := L) (G := G) (α := α)).injective
      calc
        dhjFlattenEquiv w = dhjBlockFullSubspace p V y h x := hweq
        _ = dhjFlattenEquiv (dhjBlockJoin (dhjAppend p (V x)) y h) :=
          dhjBlockFullSubspace_apply p V y h x
    rwa [hwEq] at hw
  · intro hx
    refine ⟨dhjBlockJoin (dhjAppend p (V x)) y h, hx, ?_⟩
    exact (dhjBlockFullSubspace_apply p V y h x).symm

private theorem dhjLineFree_pullback {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (A : Finset (ι → α)) (V : Combinatorics.Subspace η α ι)
    (hA : dhjLineFree A) : dhjLineFree (dhjPullback V A) := by
  intro l hl
  apply hA (V.compLine l)
  exact (dhjLineIn_compLine_iff V A l).mpr hl

private theorem dhj_column_lineEvents_eq_goodLines {k m G R t : ℕ}
    (A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)))
    (p : Fin t → Fin G → Fin (k + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin k) (Fin G))
    (y : Fin (R + 1 - (t + 1)) → Fin G → Fin (k + 1)) (ht : t ≤ R) :
    dhjColumn
        (fun l : Combinatorics.Line (Fin k) (Fin m) =>
          dhjLineEvent
            (fun z => dhjBlockSection A (dhjAppend p (Fin.castSucc ∘ V z)) (by omega)) l) y =
      dhjGoodRestrictedLines
        (dhjColumn
          (fun x : Fin m → Fin (k + 1) =>
            dhjBlockSection A
              (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y) := by
  classical
  ext l
  simp only [dhjColumn, Finset.mem_filter, Finset.mem_univ, true_and,
    dhjLineEvent, dhj_mem_goodRestrictedLines]
  constructor <;> intro hl a
  · have ha := hl a
    simpa only [dhjSubspaceMapConstants_apply] using ha
  · have ha := hl a
    have heq :
        dhjSubspaceMapConstants Fin.castSucc V (Fin.castSucc ∘ l a) =
          Fin.castSucc ∘ V (l a) :=
      dhjSubspaceMapConstants_apply Fin.castSucc V (l a)
    rw [heq] at ha
    exact ha

private noncomputable def dhjTheta (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ / (4 * dhjLineCount k m₀)

private noncomputable def dhjEta (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ * dhjTheta k m₀ δ / 48

private noncomputable def dhjGamma (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ * dhjEta k m₀ δ ^ 2 / k

private theorem dhj_constants {k m₀ : ℕ} {δ : ℝ}
    (hk : 2 ≤ k) (hm₀ : 0 < m₀) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    0 < dhjTheta k m₀ δ ∧ dhjTheta k m₀ δ ≤ 1 ∧
      0 < dhjEta k m₀ δ ∧ dhjEta k m₀ δ < dhjTheta k m₀ δ / 2 ∧
      dhjEta k m₀ δ ^ 2 / 2 ≤ δ / 2 ∧
      0 < dhjGamma k m₀ δ ∧ dhjGamma k m₀ δ ≤ dhjEta k m₀ δ ^ 2 / 2 := by
  have hlineNat : 0 < dhjLineCount k m₀ := dhjLineCount_pos hm₀
  have hline : (0 : ℝ) < dhjLineCount k m₀ := by exact_mod_cast hlineNat
  have hθpos : 0 < dhjTheta k m₀ δ := by
    simp only [dhjTheta]
    positivity
  have hden : (1 : ℝ) ≤ 4 * dhjLineCount k m₀ := by
    have : (1 : ℝ) ≤ dhjLineCount k m₀ := by exact_mod_cast hlineNat
    nlinarith
  have hθle : dhjTheta k m₀ δ ≤ 1 := by
    rw [dhjTheta, div_le_one (by positivity)]
    linarith
  have hηpos : 0 < dhjEta k m₀ δ := by
    simp only [dhjEta]
    positivity
  have hηle : dhjEta k m₀ δ ≤ δ / 48 := by
    rw [dhjEta]
    gcongr
    exact mul_le_of_le_one_right hδ.le hθle
  have hηlt : dhjEta k m₀ δ < dhjTheta k m₀ δ / 2 := by
    rw [dhjEta]
    have := hδle
    nlinarith [mul_pos hδ hθpos]
  have hηone : dhjEta k m₀ δ ≤ 1 := hηle.trans (by linarith)
  have hηsq : dhjEta k m₀ δ ^ 2 / 2 ≤ δ / 2 := by
    have hsqle : dhjEta k m₀ δ ^ 2 ≤ dhjEta k m₀ δ := by
      nlinarith [mul_nonneg hηpos.le (sub_nonneg.mpr hηone)]
    linarith
  have hγpos : 0 < dhjGamma k m₀ δ := by
    simp only [dhjGamma]
    positivity
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hγle : dhjGamma k m₀ δ ≤ dhjEta k m₀ δ ^ 2 / 2 := by
    rw [dhjGamma]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < k)]
    nlinarith [sq_nonneg (dhjEta k m₀ δ)]
  exact ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩

private theorem dhj_familyMeet_univ {k : ℕ} {ι : Type*} [Fintype ι]
    [Fintype (ι → Fin (k + 1))] :
    dhjFamilyMeet (fun _ : Fin k => (Finset.univ : Finset (ι → Fin (k + 1)))) =
      Finset.univ := by
  classical
  ext x
  simp

private theorem dhj_corollary11_blocks {k m₀ m : ℕ} {δ : ℝ}
    (hk : 2 ≤ k) (hm₀ : 0 < m₀) (hm₀m : m₀ ≤ m) (hkm : k ≤ m)
    (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : dhjAt k m₀ (δ / 4))
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ dhjEta k m₀ δ) :
    ∃ (G R : ℕ), 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)),
        δ ≤ dhjDensity A →
        dhjLineFree
          (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
            (α := Fin (k + 1))).toEmbedding) →
        ∃ (W : Combinatorics.Subspace (Fin m) (Fin (k + 1))
              (Fin (R + 1) × Fin G))
          (D : Fin k → Finset (Fin m → Fin (k + 1))),
          (∀ i, dhjInsensitive i (D i)) ∧
          dhjGamma k m₀ δ ≤ dhjDensity (dhjFamilyMeet D) ∧
          (δ + dhjGamma k m₀ δ) * dhjDensity (dhjFamilyMeet D) ≤
            dhjDensity (dhjPullback W
              (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
                (α := Fin (k + 1))).toEmbedding) ∩ dhjFamilyMeet D) := by
  classical
  obtain ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩ :=
    dhj_constants hk hm₀ hδ hδle
  obtain ⟨G, R, hG, hregular⟩ :=
    dhj_lemma7_blocks (by omega) hm₀ hm₀m hδ
      (by positivity : 0 < dhjEta k m₀ δ ^ 2 / 2)
      hηsq hDHJ
  refine ⟨G, R, hG, ?_⟩
  intro A hA hlineFree
  obtain ⟨t, ht, p, V, hsections, hlines⟩ := hregular A hA
  obtain hhigh | hlow := dhj_lemma8_blocks (by omega) (hm₀.trans_le hm₀m)
    hηpos hθpos hηlt ht A p V hsections hlines
  · obtain ⟨y, hy⟩ := hhigh
    let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
      (by omega : t + 1 ≤ R + 1)
    let B := dhjColumn
      (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y
    let D : Fin k → Finset (Fin m → Fin (k + 1)) := fun _ => Finset.univ
    have hpull : dhjPullback W
        (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
          (α := Fin (k + 1))).toEmbedding) = B := by
      exact dhjPullback_blockFullSubspace A p
        (dhjSubspaceMapConstants Fin.castSucc V) y (by omega)
    have hmeet : dhjFamilyMeet D = Finset.univ := dhj_familyMeet_univ
    refine ⟨W, D, ?_, ?_, ?_⟩
    · intro i
      exact dhjInsensitive_univ i
    · rw [hmeet, dhjDensity_univ]
      exact hγle.trans (hηsq.trans (by linarith))
    · rw [hmeet, dhjDensity_univ, mul_one, Finset.inter_univ, hpull]
      calc
        δ + dhjGamma k m₀ δ ≤ δ + dhjEta k m₀ δ ^ 2 / 2 :=
          by linarith
        _ ≤ dhjDensity B := by simpa [B] using hy
  · obtain ⟨y, hyden, hygood⟩ := hlow
    let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
      (by omega : t + 1 ≤ R + 1)
    let B := dhjColumn
      (fun x : Fin m → Fin (k + 1) => dhjBlockSection A
        (dhjAppend p (dhjSubspaceMapConstants Fin.castSucc V x)) (by omega)) y
    have hpull : dhjPullback W
        (A.map (dhjFlattenEquiv (L := R + 1) (G := G)
          (α := Fin (k + 1))).toEmbedding) = B := by
      exact dhjPullback_blockFullSubspace A p
        (dhjSubspaceMapConstants Fin.castSucc V) y (by omega)
    have hBlineFree : dhjLineFree B := by
      rw [← hpull]
      exact dhjLineFree_pullback _ W hlineFree
    have hgood : dhjTheta k m₀ δ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B) := by
      rw [← dhj_column_lineEvents_eq_goodLines A p V y ht]
      exact hygood
    obtain ⟨D, hDi, hDmass, hDcorr⟩ :=
      dhj_corollary11_cube (by omega) hkm hδ hδle hθpos hθle rfl rfl hratio B
        hBlineFree hyden hgood
    refine ⟨W, D, hDi, hDmass, ?_⟩
    rwa [hpull]

private theorem dhj_exists_restricted_subspace_type {k d : ℕ} {β : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hβ : 0 < β) (hβle : β ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ P R : ℕ, 0 < P ∧
      ∀ E : Finset (Fin (R + 1) × Fin P → Fin (k + 1)), β ≤ dhjDensity E →
        ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1))
            (Fin (R + 1) × Fin P),
          ∀ x : Fin d → Fin k, V (Fin.castSucc ∘ x) ∈ E := by
  classical
  obtain ⟨P, hP⟩ := dhjMultiThreshold (by omega) hDHJ d (β / 4) (by positivity)
  let _ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hPpos : 0 < P := by
    have hsmall : β / 4 ≤ (1 : ℝ) := by linarith
    have huniv : dhjDensity
        (Finset.univ : Finset (Fin P → Fin k)) = 1 := dhjDensity_univ
    obtain ⟨V, hV⟩ := hP Finset.univ (by rw [huniv]; exact hsmall)
    obtain ⟨j, hj⟩ := V.proper ⟨0, hd⟩
    exact Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ j)
  let X := Fin P → Fin (k + 1)
  have hXcard : 2 ≤ Fintype.card X := by
    dsimp only [X]
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact (by omega : 2 ≤ k + 1).trans (Nat.le_pow hPpos)
  obtain ⟨R, hR⟩ := dhj_exists_regular_length hXcard (show 0 < β / 2 by positivity)
  refine ⟨P, R, hPpos, ?_⟩
  intro E hE
  let e := dhjFlattenEquiv (L := R + 1) (G := P) (α := Fin (k + 1))
  let A : Finset (Fin (R + 1) → X) := E.map e.symm.toEmbedding
  have hAdens : dhjDensity A = dhjDensity E := dhjDensity_map_equiv e.symm E
  obtain ⟨t, ht, p, hp⟩ :=
    dhj_exists_regular_blockSection hXcard R A (show 0 < β / 2 by positivity) hR
  let Erow : (Fin P → Fin k) →
      Finset (Fin (R + 1 - (t + 1)) → X) := fun z =>
    dhjBlockSection A (dhjAppend p (Fin.castSucc ∘ z)) (by omega)
  have hrows : ∀ z, β / 2 ≤ dhjDensity (Erow z) := by
    intro z
    calc
      β / 2 ≤ dhjDensity A - β / 2 := by rw [hAdens]; linarith
      _ ≤ dhjDensity (Erow z) := hp (Fin.castSucc ∘ z)
  let H := dhjDenseColumns Erow (β / 2)
  have hHdensity : β / 4 ≤ dhjDensity H := by
    have h := dhjDensity_denseColumns Erow (show 0 < β / 2 by positivity) hrows
    change β / 4 ≤ dhjDensity (dhjDenseColumns Erow (β / 2))
    convert h using 1; ring
  have hHne : H.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, dhjDensity_empty] at hHdensity
    linarith
  obtain ⟨y, hyH⟩ := hHne
  have hy : β / 4 ≤ dhjDensity (dhjColumn Erow y) := by
    have h := (Finset.mem_filter.mp hyH).2
    convert h using 1; ring
  obtain ⟨V, hV⟩ := hP (dhjColumn Erow y) hy
  let W := dhjBlockFullSubspace p (dhjSubspaceMapConstants Fin.castSucc V) y
    (by omega : t + 1 ≤ R + 1)
  refine ⟨W, ?_⟩
  intro x
  have hxcol : V x ∈ dhjColumn Erow y := hV x
  have hyrow : y ∈ Erow (V x) := by
    simpa only [dhjColumn, Finset.mem_filter, Finset.mem_univ, true_and] using hxcol
  have hblock : dhjBlockJoin (dhjAppend p (Fin.castSucc ∘ V x)) y (by omega) ∈ A := by
    simpa only [Erow, dhjBlockSection, Finset.mem_filter, Finset.mem_univ, true_and]
      using hyrow
  have hflat :
      dhjFlattenBlocks (dhjBlockJoin (dhjAppend p (Fin.castSucc ∘ V x)) y (by omega))
        ∈ E := by
    change e (dhjBlockJoin (dhjAppend p (Fin.castSucc ∘ V x)) y (by omega)) ∈ E
    simpa [A] using hblock
  rw [dhjBlockFullSubspace_apply, dhjSubspaceMapConstants_apply]
  exact hflat

private def dhjBlockCore {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (w : Fin L → J → Fin (k + 1)) : Fin L → J → Fin (k + 1) :=
  fun b => dhjReplaceLast i (w b)

private def dhjBlockInsensitive {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (D : Finset (Fin L → J → Fin (k + 1))) : Prop :=
  ∀ w, w ∈ D ↔ dhjBlockCore i w ∈ D

private theorem dhjBlockCore_idem {k : ℕ} {J : Type*} (i : Fin k) {L : ℕ}
    (w : Fin L → J → Fin (k + 1)) :
    dhjBlockCore i (dhjBlockCore i w) = dhjBlockCore i w := by
  funext b j
  exact congrFun (dhjReplaceLast_idem i (w b)) j

private theorem dhjBlockInsensitive.congr_core {k : ℕ} {J : Type*} {i : Fin k} {L : ℕ}
    {D : Finset (Fin L → J → Fin (k + 1))} (hD : dhjBlockInsensitive i D)
    {x y : Fin L → J → Fin (k + 1)} (hxy : dhjBlockCore i x = dhjBlockCore i y) :
    x ∈ D ↔ y ∈ D := by
  calc
    x ∈ D ↔ dhjBlockCore i x ∈ D := hD x
    _ ↔ dhjBlockCore i y ∈ D := by rw [hxy]
    _ ↔ y ∈ D := (hD y).symm

private theorem dhjBlockInsensitive_sdiff {k : ℕ} {J : Type*}
    {i : Fin k} {L : ℕ} [DecidableEq (Fin L → J → Fin (k + 1))]
    {A B : Finset (Fin L → J → Fin (k + 1))}
    (hA : dhjBlockInsensitive i A) (hB : dhjBlockInsensitive i B) :
    dhjBlockInsensitive i (A \ B) := by
  intro w
  simp only [Finset.mem_sdiff]
  rw [hA w, hB w]

private theorem dhjFlattenBlocks_blockCore {k L : ℕ} {J : Type*} (i : Fin k)
    (w : Fin L → J → Fin (k + 1)) :
    (fun q : Fin L × J => dhjBlockCore i w q.1 q.2) =
      dhjReplaceLast i (fun q : Fin L × J => w q.1 q.2) := by
  rfl

private def dhjCurryEquiv {L : ℕ} {J α : Type*} :
    (Fin L → J → α) ≃ (Fin L × J → α) where
  toFun w q := w q.1 q.2
  invFun f b j := f (b, j)
  left_inv _ := rfl
  right_inv f := by
    funext q
    rcases q with ⟨b, j⟩
    rfl

private theorem dhjBlockInsensitive_map_flatten {k L : ℕ} {J : Type*}
    (i : Fin k) (D : Finset (Fin L × J → Fin (k + 1)))
    (hD : dhjInsensitive i D) :
    dhjBlockInsensitive i
      (D.map (dhjCurryEquiv (L := L) (J := J) (α := Fin (k + 1))).symm.toEmbedding) := by
  classical
  let e := dhjCurryEquiv (L := L) (J := J) (α := Fin (k + 1))
  intro w
  have hmem (u : Fin L → J → Fin (k + 1)) :
      u ∈ D.map e.symm.toEmbedding ↔ e u ∈ D := by
    simp [e]
  rw [hmem, hmem]
  have hcore : e (dhjBlockCore i w) = dhjReplaceLast i (e w) := by
    rfl
  rw [hcore]
  exact hD (e w)

private def dhjMiddleWord {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (p : Fin t → X) (z : X) (y : Fin (Q - (t + 1)) → X) : Fin Q → X :=
  fun q =>
    if hqt : q.val < t then p ⟨q.val, hqt⟩
    else if hqeq : q.val = t then z
    else y ⟨q.val - (t + 1), by omega⟩

private def dhjMiddleEquiv {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q) :
    (Fin Q → X) ≃
      (((Fin t → X) × (Fin (Q - (t + 1)) → X)) × X) where
  toFun w :=
    ((fun i => w ⟨i.val, by omega⟩,
      fun j => w ⟨t + 1 + j.val, by omega⟩),
      w ⟨t, by omega⟩)
  invFun q := dhjMiddleWord h q.1.1 q.2 q.1.2
  left_inv w := by
    funext q
    by_cases hqt : q.val < t
    · simp [dhjMiddleWord, hqt]
    · by_cases hqeq : q.val = t
      · subst hqeq
        simp [dhjMiddleWord]
      · simp only [dhjMiddleWord, hqt, hqeq, ↓reduceDIte]
        apply congrArg w
        apply Fin.ext
        simp
        omega
  right_inv q := by
    rcases q with ⟨⟨p, y⟩, z⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        simp [dhjMiddleWord]
      · funext j
        simp only [dhjMiddleWord]
        have hnot : ¬ t + 1 + j.val < t := by omega
        have hne : t + 1 + j.val ≠ t := by omega
        simp [hnot, hne]
    · simp [dhjMiddleWord]

private noncomputable def dhjMiddleSection {X : Type*} [Fintype X] {Q t : ℕ}
    (R : Finset (Fin Q → X)) (h : t + 1 ≤ Q)
    (b : (Fin t → X) × (Fin (Q - (t + 1)) → X)) : Finset X := by
  classical
  exact Finset.univ.filter fun z => dhjMiddleWord h b.1 z b.2 ∈ R

@[simp]
private theorem dhj_mem_middleSection {X : Type*} [Fintype X] {Q t : ℕ}
    (R : Finset (Fin Q → X)) (h : t + 1 ≤ Q)
    (b : (Fin t → X) × (Fin (Q - (t + 1)) → X)) (z : X) :
    z ∈ dhjMiddleSection R h b ↔ dhjMiddleWord h b.1 z b.2 ∈ R := by
  classical
  simp [dhjMiddleSection]

private noncomputable def dhjProdSection {B X : Type*} [Fintype X]
    (A : Finset (B × X)) (b : B) : Finset X := by
  classical
  exact Finset.univ.filter fun x => (b, x) ∈ A

private theorem dhj_card_eq_sum_prodSections {B X : Type*}
    [Fintype B] [Fintype X] (A : Finset (B × X)) :
    A.card = ∑ b : B, (dhjProdSection A b).card := by
  classical
  calc
    A.card = ∑ b ∈ (Finset.univ : Finset B),
        (A.filter fun q => q.1 = b).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro q hq
      simp
    _ = ∑ b : B, (dhjProdSection A b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      symm
      apply Finset.card_bij (fun x _ => (b, x))
      · intro x hx
        simp only [dhjProdSection, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp [hx]
      · intro x₁ hx₁ x₂ hx₂ h
        exact congrArg Prod.snd h
      · intro q hq
        have hqb : q.1 = b := (Finset.mem_filter.mp hq).2
        refine ⟨q.2, ?_, ?_⟩
        · simp only [dhjProdSection, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hqb]
          simpa using (Finset.mem_filter.mp hq).1
        · exact Prod.ext hqb.symm rfl

private theorem dhj_density_eq_expect_prodSections {B X : Type*}
    [Fintype B] [Nonempty B] [Fintype X] [Nonempty X]
    (A : Finset (B × X)) :
    dhjDensity A = Finset.expect Finset.univ fun b : B =>
      dhjDensity (dhjProdSection A b) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [dhjDensity, dhj_card_eq_sum_prodSections, Nat.cast_sum,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div, div_div]
  congr 1
  ring

private theorem dhj_middleSection_map {X : Type*} [Fintype X] {Q t : ℕ}
    (R : Finset (Fin Q → X)) (h : t + 1 ≤ Q)
    (b : (Fin t → X) × (Fin (Q - (t + 1)) → X)) :
    dhjProdSection (R.map (dhjMiddleEquiv h).toEmbedding) b =
      dhjMiddleSection R h b := by
  classical
  ext z
  simp only [dhjProdSection, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, dhj_mem_middleSection]
  constructor
  · rintro ⟨w, hw, heq⟩
    have hwEq : w = dhjMiddleWord h b.1 z b.2 := by
      let e := dhjMiddleEquiv (X := X) h
      calc
        w = e.symm (e w) := (e.symm_apply_apply w).symm
        _ = e.symm (b, z) := congrArg e.symm heq
        _ = dhjMiddleWord h b.1 z b.2 := rfl
    rwa [hwEq] at hw
  · intro hw
    refine ⟨dhjMiddleWord h b.1 z b.2, hw, ?_⟩
    let e := dhjMiddleEquiv (X := X) h
    change e (e.symm (b, z)) = (b, z)
    exact e.apply_symm_apply (b, z)

private theorem dhj_density_eq_expect_middleSections {X : Type*}
    [Fintype X] [Nonempty X] {Q t : ℕ} (h : t + 1 ≤ Q)
    (R : Finset (Fin Q → X)) :
    dhjDensity R = Finset.expect Finset.univ fun
      b : (Fin t → X) × (Fin (Q - (t + 1)) → X) =>
        dhjDensity (dhjMiddleSection R h b) := by
  let e := dhjMiddleEquiv (X := X) h
  have hmap : dhjDensity (R.map e.toEmbedding) = dhjDensity R :=
    dhjDensity_map_equiv e R
  rw [← hmap, dhj_density_eq_expect_prodSections]
  apply Finset.expect_congr rfl
  intro b hb
  rw [dhj_middleSection_map]

private theorem dhj_superlevel_density_of_double_le_average {Y : Type*}
    [Fintype Y] [Nonempty Y] (f : Y → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (_hβle : β ≤ 1) (hf : ∀ y, f y ≤ 1)
    (havg : 2 * β ≤ Finset.expect Finset.univ f) :
    β ≤ dhjDensity (dhjSuperlevel f β) := by
  classical
  let T := dhjSuperlevel f β
  have hpoint : ∀ y ∈ (Finset.univ : Finset Y),
      f y ≤ if y ∈ T then 1 else β := by
    intro y hy
    by_cases hyT : y ∈ T
    · simp [hyT, hf y]
    · simp only [hyT, ↓reduceIte]
      exact (lt_of_not_ge (by simpa [T, dhjSuperlevel] using hyT)).le
  have hsumUpper : (∑ y : Y, f y) ≤
      T.card + (Fintype.card Y - T.card) * β := by
    calc
      (∑ y : Y, f y) ≤ ∑ y : Y, (if y ∈ T then (1 : ℝ) else β) :=
        Finset.sum_le_sum hpoint
      _ = T.card + (Fintype.card Y - T.card) * β := by
        rw [Finset.sum_ite]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [Finset.filter_notMem_eq_sdiff]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_sdiff_of_subset T.subset_univ, Finset.card_univ,
          Nat.cast_sub T.card_le_univ]
  have hsumLower : 2 * β * Fintype.card Y ≤ ∑ y : Y, f y := by
    rw [Fintype.expect_eq_sum_div_card, le_div_iff₀ (by positivity)] at havg
    nlinarith
  change β ≤ (T.card : ℝ) / Fintype.card Y
  rw [le_div_iff₀ (by positivity)]
  have hcard : (T.card : ℝ) ≤ Fintype.card Y := by exact_mod_cast T.card_le_univ
  nlinarith [mul_nonneg (sub_nonneg.mpr _hβle) (Nat.cast_nonneg T.card)]

private def dhjJoinAt {X : Type*} {Q t : ℕ} (h : t ≤ Q)
    (p : Fin t → X) (y : Fin (Q - t) → X) : Fin Q → X :=
  fun q => if hqt : q.val < t then p ⟨q.val, hqt⟩
    else y ⟨q.val - t, by omega⟩

private def dhjTailCons {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (z : X) (y : Fin (Q - (t + 1)) → X) : Fin (Q - t) → X :=
  fun q => if hq : q.val = 0 then z else y ⟨q.val - 1, by omega⟩

private theorem dhjJoinAt_tailCons {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (p : Fin t → X) (z : X) (y : Fin (Q - (t + 1)) → X) :
    dhjJoinAt (by omega) p (dhjTailCons h z y) = dhjMiddleWord h p z y := by
  funext q
  by_cases hqt : q.val < t
  · simp [dhjJoinAt, dhjMiddleWord, hqt]
  · by_cases hqeq : q.val = t
    · subst hqeq
      simp [dhjJoinAt, dhjMiddleWord, dhjTailCons]
    · simp only [dhjJoinAt, dhjMiddleWord, hqt, hqeq, ↓reduceDIte,
        dhjTailCons]
      rw [dite_eq_right (by omega)]
      congr 1

private theorem dhjJoinAt_append {X : Type*} {Q t : ℕ} (h : t + 1 ≤ Q)
    (p : Fin t → X) (z : X) (y : Fin (Q - (t + 1)) → X) :
    dhjJoinAt h (dhjAppend p z) y = dhjMiddleWord h p z y := by
  funext q
  by_cases hqt : q.val < t
  · simp only [dhjJoinAt, dhjMiddleWord, hqt, ↓reduceDIte]
    rw [dite_eq_left (by omega : q.val < t + 1)]
    have happ : dhjAppend p z (Fin.castSucc (⟨q.val, hqt⟩ : Fin t)) =
        p ⟨q.val, hqt⟩ := by
      exact Fin.lastCases_castSucc _
    let qi : Fin (t + 1) := ⟨q.val, by omega⟩
    change dhjAppend p z qi = p ⟨q.val, hqt⟩
    have hqi : qi = Fin.castSucc (⟨q.val, hqt⟩ : Fin t) := by
      apply Fin.ext
      rfl
    rw [hqi]
    exact happ
  · by_cases hqeq : q.val = t
    · simp only [dhjJoinAt, dhjMiddleWord, hqeq, ↓reduceDIte]
      simp only [dite_eq_left (by omega : t < t + 1), dite_eq_right (lt_irrefl t)]
      have happ : dhjAppend p z (Fin.last t) = z := Fin.lastCases_last
      let qi : Fin (t + 1) := ⟨t, by omega⟩
      change dhjAppend p z qi = z
      have hqi : qi = Fin.last t := by
        apply Fin.ext
        rfl
      rw [hqi]
      exact happ
    · simp only [dhjJoinAt, dhjMiddleWord, hqt, hqeq, ↓reduceDIte]
      rw [dite_eq_right (by omega : ¬q.val < t + 1)]

private def dhjStageInsensitive {k Q t : ℕ} {J : Type*} (i : Fin k)
    (R : Finset (Fin Q → J → Fin (k + 1))) (h : t ≤ Q) : Prop :=
  ∀ (p : Fin t → J → Fin (k + 1))
    (y y' : Fin (Q - t) → J → Fin (k + 1)),
    dhjBlockCore i y = dhjBlockCore i y' →
      (dhjJoinAt h p y ∈ R ↔ dhjJoinAt h p y' ∈ R)

private theorem dhjStageInsensitive_zero {k Q : ℕ} {J : Type*} (i : Fin k)
    (R : Finset (Fin Q → J → Fin (k + 1)))
    (hR : dhjBlockInsensitive i R) :
    dhjStageInsensitive i R (Nat.zero_le Q) := by
  intro p y y' hyy'
  apply hR.congr_core
  funext b j
  have hb := congrFun (congrFun hyy' b) j
  simpa [dhjJoinAt, dhjBlockCore] using hb

private theorem dhjStageInsensitive.middleSection {k Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (i : Fin k)
    (R : Finset (Fin Q → J → Fin (k + 1))) (h : t + 1 ≤ Q)
    (hR : dhjStageInsensitive (t := t) i R (by omega))
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))) :
    dhjInsensitive i (dhjMiddleSection (X := J → Fin (k + 1)) R h b) := by
  intro z
  rw [dhj_mem_middleSection, dhj_mem_middleSection]
  rw [← dhjJoinAt_tailCons h b.1 z b.2,
    ← dhjJoinAt_tailCons h b.1 (dhjReplaceLast i z) b.2]
  have hcore :
      dhjBlockCore i (dhjTailCons h z b.2) =
        dhjBlockCore i (dhjTailCons h (dhjReplaceLast i z) b.2) := by
    funext q j
    by_cases hq : q.val = 0
    · simp [dhjBlockCore, dhjTailCons, hq, dhjReplaceLast_idem]
    · simp [dhjBlockCore, dhjTailCons, hq]
  have hs := hR b.1 (dhjTailCons h z b.2)
    (dhjTailCons h (dhjReplaceLast i z) b.2) hcore
  exact hs

private theorem dhjSubspace_replaceLast {k d : ℕ} {J : Type*} (i : Fin k)
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
    (z : Fin d → Fin (k + 1)) :
    dhjReplaceLast i (V z) =
      dhjReplaceLast i (V (Fin.castSucc ∘ dhjDropLast i z)) := by
  funext q
  cases hq : V.idxFun q with
  | inl a =>
      simp [dhjReplaceLast, dhjDropLast, Combinatorics.Subspace.coe_apply, hq]
  | inr e =>
      generalize hze : z e = a
      cases a using Fin.lastCases <;>
        simp [dhjReplaceLast, dhjDropLast, Combinatorics.Subspace.coe_apply, hq, hze]

private theorem dhjInsensitive.subspaceIn {k d : ℕ} {J : Type*} (i : Fin k)
    (E : Finset (J → Fin (k + 1))) (hE : dhjInsensitive i E)
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
    (hV : ∀ x : Fin d → Fin k, V (Fin.castSucc ∘ x) ∈ E) :
    ∀ z, V z ∈ E := by
  intro z
  rw [hE (V z), dhjSubspace_replaceLast i V z, ← hE]
  exact hV (dhjDropLast i z)

private def dhjBaseSuffixInsensitive {k Q t : ℕ} {J : Type*} (i : Fin k)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))) : Prop :=
  ∀ (p : Fin t → J → Fin (k + 1))
    (y y' : Fin (Q - (t + 1)) → J → Fin (k + 1)),
    dhjBlockCore i y = dhjBlockCore i y' → ((p, y) ∈ S ↔ (p, y') ∈ S)

private theorem dhj_tiling_step_data {k d Q t : ℕ} {J : Type*}
    [Fintype J] [Fintype (J → Fin (k + 1))]
    (i : Fin k) (h : t + 1 ≤ Q) {β : ℝ} (hβ : 0 < β) (hβle : β ≤ 1)
    (hRestr : ∀ E : Finset (J → Fin (k + 1)), β ≤ dhjDensity E →
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J,
        ∀ x : Fin d → Fin k, V (Fin.castSucc ∘ x) ∈ E)
    (R : Finset (Fin Q → J → Fin (k + 1)))
    (hRden : 2 * β ≤ dhjDensity R)
    (hRins : dhjStageInsensitive (t := t) i R (by omega)) :
    ∃ (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
      (S : Finset ((Fin t → J → Fin (k + 1)) ×
        (Fin (Q - (t + 1)) → J → Fin (k + 1)))),
      β / Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) ≤
        dhjDensity S ∧
      (∀ b ∈ S, ∀ z, V z ∈ dhjMiddleSection R h b) ∧
      dhjBaseSuffixInsensitive i S := by
  classical
  let X := J → Fin (k + 1)
  let B := (Fin t → X) × (Fin (Q - (t + 1)) → X)
  let f : B → ℝ := fun b => dhjDensity (dhjMiddleSection R h b)
  let T := dhjSuperlevel f β
  have hTmass : β ≤ dhjDensity T := by
    apply dhj_superlevel_density_of_double_le_average f hβ.le hβle
    · intro b
      exact dhjDensity_le_one _
    · rw [← dhj_density_eq_expect_middleSections h R]
      exact hRden
  have hTne : T.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, dhjDensity_empty] at hTmass
    linarith
  have hVAt (b : B) (hb : b ∈ T) :
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J,
        ∀ z, V z ∈ dhjMiddleSection R h b := by
    have hbden : β ≤ dhjDensity (dhjMiddleSection R h b) :=
      (Finset.mem_filter.mp hb).2
    obtain ⟨V, hV⟩ := hRestr _ hbden
    refine ⟨V, (hRins.middleSection i R h b).subspaceIn i _ V hV⟩
  obtain ⟨b₀, hb₀⟩ := hTne
  obtain ⟨V₀, hV₀⟩ := hVAt b₀ hb₀
  let chosen : B → Combinatorics.Subspace (Fin d) (Fin (k + 1)) J := fun b =>
    if hb : b ∈ T then Classical.choose (hVAt b hb) else V₀
  have hchosen (b : B) (hb : b ∈ T) :
      ∀ z, chosen b z ∈ dhjMiddleSection R h b := by
    simpa [chosen, hb] using Classical.choose_spec (hVAt b hb)
  let _ : Nonempty (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) := ⟨V₀⟩
  obtain ⟨V, hVfiber⟩ := dhj_exists_dense_fiber T chosen
  let F := T.filter fun b => chosen b = V
  let S : Finset B := Finset.univ.filter fun b =>
    ∀ z, V z ∈ dhjMiddleSection R h b
  have hFS : F ⊆ S := by
    intro b hb
    have hbT : b ∈ T := (Finset.mem_filter.mp hb).1
    have hbV : chosen b = V := (Finset.mem_filter.mp hb).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro z
    rw [← hbV]
    exact hchosen b hbT z
  have hSmass :
      β / Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) ≤
        dhjDensity S := by
    calc
      β / Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) ≤
          dhjDensity T /
            Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) := by
        gcongr
      _ ≤ dhjDensity F := by simpa [F] using hVfiber
      _ ≤ dhjDensity S := dhjDensity_mono hFS
  refine ⟨V, S, hSmass, ?_, ?_⟩
  · intro b hb z
    exact (Finset.mem_filter.mp hb).2 z
  · intro p y y' hyy'
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hmem z
    · have hz := hmem z
      rw [dhj_mem_middleSection] at hz ⊢
      change dhjMiddleWord h p (V z) y ∈ R at hz
      change dhjMiddleWord h p (V z) y' ∈ R
      rw [← dhjJoinAt_tailCons h p (V z) y] at hz
      rw [← dhjJoinAt_tailCons h p (V z) y']
      apply (hRins p _ _ ?_).mp hz
      funext q j
      by_cases hq : q.val = 0
      · simp [dhjBlockCore, dhjTailCons, hq]
      · have := congrFun (congrFun hyy' ⟨q.val - 1, by omega⟩) j
        simpa [dhjBlockCore, dhjTailCons, hq] using this
    · have hz := hmem z
      rw [dhj_mem_middleSection] at hz ⊢
      change dhjMiddleWord h p (V z) y' ∈ R at hz
      change dhjMiddleWord h p (V z) y ∈ R
      rw [← dhjJoinAt_tailCons h p (V z) y'] at hz
      rw [← dhjJoinAt_tailCons h p (V z) y]
      apply (hRins p _ _ ?_).mp hz
      funext q j
      by_cases hq : q.val = 0
      · simp [dhjBlockCore, dhjTailCons, hq]
      · have := congrFun (congrFun hyy'.symm ⟨q.val - 1, by omega⟩) j
        simpa [dhjBlockCore, dhjTailCons, hq] using this

private theorem dhjDensity_product {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Finset X) (B : Finset Y) :
    dhjDensity (A.product B) = dhjDensity A * dhjDensity B := by
  classical
  have hcard : (A.product B).card = A.card * B.card := Finset.card_product A B
  unfold dhjDensity
  rw [hcard, Fintype.card_prod]
  push_cast
  rw [div_mul_div_comm]

private noncomputable def dhjBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Finset (Fin Q → J → Fin (k + 1)) := by
  classical
  exact (S.product (dhjSubspacePoints V)).map (dhjMiddleEquiv h).symm.toEmbedding

private theorem dhj_mem_batch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
    (w : Fin Q → J → Fin (k + 1)) :
    w ∈ dhjBatch h S V ↔
      (dhjMiddleEquiv h w).1 ∈ S ∧
        (dhjMiddleEquiv h w).2 ∈ dhjSubspacePoints V := by
  classical
  let e := dhjMiddleEquiv (X := J → Fin (k + 1)) h
  constructor
  · intro hw
    obtain ⟨q, hq, hqw⟩ := Finset.mem_map.mp hw
    have heq : q = e w := by
      calc
        q = e (e.symm q) := (e.apply_symm_apply q).symm
        _ = e w := congrArg e hqw
    rw [← heq]
    exact Finset.mem_product.mp hq
  · intro hw
    rw [dhjBatch, Finset.mem_map]
    exact ⟨e w, Finset.mem_product.mpr hw, e.symm_apply_apply w⟩

private theorem dhjDensity_batch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjDensity (dhjBatch h S V) =
      dhjDensity S * dhjDensity (dhjSubspacePoints V) := by
  rw [dhjBatch, dhjDensity_map_equiv, dhjDensity_product]

private def dhjMiddleSubspace {k d Q t : ℕ} {J : Type*}
    (h : t + 1 ≤ Q)
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin Q × J) where
  idxFun q :=
    if hqt : q.1.val < t then Sum.inl (b.1 ⟨q.1.val, hqt⟩ q.2)
    else if hqeq : q.1.val = t then V.idxFun q.2
    else Sum.inl (b.2 ⟨q.1.val - (t + 1), by omega⟩ q.2)
  proper e := by
    obtain ⟨j, hj⟩ := V.proper e
    refine ⟨(⟨t, by omega⟩, j), ?_⟩
    simp [hj]

private theorem dhjMiddleSubspace_apply {k d Q t : ℕ} {J : Type*}
    (h : t + 1 ≤ Q)
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
    (z : Fin d → Fin (k + 1)) :
    dhjMiddleSubspace h b V z =
      dhjCurryEquiv (dhjMiddleWord h b.1 (V z) b.2) := by
  funext q
  rcases q with ⟨q, j⟩
  by_cases hqt : q.val < t
  · simp [dhjMiddleSubspace, dhjMiddleWord,
      Combinatorics.Subspace.coe_apply, hqt, dhjCurryEquiv]
  · by_cases hqeq : q.val = t
    · simp [dhjMiddleSubspace, dhjMiddleWord,
        Combinatorics.Subspace.coe_apply, hqeq, dhjCurryEquiv]
    · simp [dhjMiddleSubspace, dhjMiddleWord,
        Combinatorics.Subspace.coe_apply, hqt, hqeq, dhjCurryEquiv]

private noncomputable def dhjFlatBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    Finset (Fin Q × J → Fin (k + 1)) := by
  classical
  exact (dhjBatch h S V).map
    (dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).toEmbedding

private theorem dhj_mem_flatBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
    (w : Fin Q × J → Fin (k + 1)) :
    w ∈ dhjFlatBatch h S V ↔
      (dhjMiddleEquiv h
        ((dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).symm w)).1 ∈ S ∧
      (dhjMiddleEquiv h
        ((dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).symm w)).2 ∈
        dhjSubspacePoints V := by
  classical
  let e := dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))
  constructor
  · intro hw
    obtain ⟨u, hu, huw⟩ := Finset.mem_map.mp hw
    have hu' := (dhj_mem_batch h S V u).mp hu
    change (dhjMiddleEquiv h (e.symm w)).1 ∈ S ∧
      (dhjMiddleEquiv h (e.symm w)).2 ∈ dhjSubspacePoints V
    have huw' : e u = w := huw
    have he : e.symm w = u := by
      rw [← huw']
      exact e.symm_apply_apply u
    rw [he]
    exact hu'
  · intro hw
    rw [dhjFlatBatch, Finset.mem_map]
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    exact (dhj_mem_batch h S V (e.symm w)).mpr hw

private theorem dhjFlatBatch_singleton {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjFlatBatch h {b} V = dhjSubspacePoints (dhjMiddleSubspace h b V) := by
  classical
  let e := dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))
  let m := dhjMiddleEquiv (X := J → Fin (k + 1)) h
  ext w
  rw [dhj_mem_flatBatch]
  constructor
  · intro hw
    have hb : (m (e.symm w)).1 = b := by simpa [e, m] using hw.1
    obtain ⟨z, hz⟩ := (dhj_mem_subspacePoints V _).mp hw.2
    apply (dhj_mem_subspacePoints (dhjMiddleSubspace h b V) w).mpr
    refine ⟨z, ?_⟩
    rw [dhjMiddleSubspace_apply]
    change e (dhjMiddleWord h b.1 (V z) b.2) = w
    calc
      e (dhjMiddleWord h b.1 (V z) b.2) = e (m.symm (m (e.symm w))) := by
        apply congrArg e
        change m.symm (b, V z) = m.symm (m (e.symm w))
        apply congrArg m.symm
        exact Prod.ext hb.symm hz
      _ = w := by simp [e, m]
  · intro hw
    obtain ⟨z, rfl⟩ := (dhj_mem_subspacePoints (dhjMiddleSubspace h b V) w).mp hw
    have hcoord :
        m (e.symm (dhjMiddleSubspace h b V z)) = (b, V z) := by
      rw [dhjMiddleSubspace_apply]
      change m (e.symm (e (m.symm (b, V z)))) = (b, V z)
      simp
    constructor
    · rw [hcoord]
      simp
    · rw [hcoord]
      exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩

private theorem dhjFlatBatch_insert {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))]
    [DecidableEq ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))]
    [DecidableEq (Fin Q × J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjFlatBatch h (insert b S) V =
      dhjFlatBatch h S V ∪ dhjFlatBatch h {b} V := by
  classical
  ext w
  simp only [dhj_mem_flatBatch, Finset.mem_insert, Finset.mem_union,
    Finset.mem_singleton]
  tauto

private theorem dhjFlatBatch_disjoint_singleton {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (b : (Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1)))
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) (hb : b ∉ S) :
    Disjoint (dhjFlatBatch h S V) (dhjFlatBatch h {b} V) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwS hwb
  have hwS' := (dhj_mem_flatBatch h S V w).mp hwS
  have hwb' := (dhj_mem_flatBatch h {b} V w).mp hwb
  have hbase :
      (dhjMiddleEquiv h
        ((dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).symm w)).1 = b :=
    Finset.mem_singleton.mp hwb'.1
  exact hb (hbase ▸ hwS'.1)

private theorem dhjTiled_flatBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))]
    [DecidableEq (Fin Q × J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjTiled d k (dhjFlatBatch h S V) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hempty : dhjFlatBatch h ∅ V = ∅ := by
        ext w
        simp only [dhj_mem_flatBatch, Finset.notMem_empty, false_and,
          Finset.notMem_empty]
      rw [hempty]
      exact dhjTiled.empty
  | @insert b S hb ih =>
      rw [dhjFlatBatch_insert h b S V, dhjFlatBatch_singleton h b V]
      have hdis := dhjFlatBatch_disjoint_singleton h b S V hb
      rw [dhjFlatBatch_singleton h b V] at hdis
      exact dhjTiled.add _ _ ih hdis

private theorem dhjBatch_subset {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (R : Finset (Fin Q → J → Fin (k + 1)))
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)
    (hS : ∀ b ∈ S, ∀ z, V z ∈ dhjMiddleSection R h b) :
    dhjBatch h S V ⊆ R := by
  classical
  intro w hw
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
  obtain ⟨hb, hz⟩ := Finset.mem_product.mp hq
  rcases q with ⟨b, u⟩
  obtain ⟨z, hVz⟩ := (dhj_mem_subspacePoints V u).mp hz
  subst u
  have hmem := hS b hb z
  rwa [dhj_mem_middleSection] at hmem

private theorem dhjDensity_flatBatch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))]
    [Fintype (Fin Q × J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjDensity (dhjFlatBatch h S V) =
      dhjDensity S * dhjDensity (dhjSubspacePoints V) := by
  rw [dhjFlatBatch, dhjDensity_map_equiv, dhjDensity_batch]

private theorem dhjStageInsensitive_sdiff_batch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))]
    [DecidableEq (Fin Q → J → Fin (k + 1))]
    (i : Fin k) (h : t + 1 ≤ Q)
    (R : Finset (Fin Q → J → Fin (k + 1)))
    (hR : dhjStageInsensitive (t := t) i R (by omega))
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (hS : dhjBaseSuffixInsensitive i S)
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjStageInsensitive (t := t + 1) i (R \ dhjBatch h S V) h := by
  intro p' y y' hyy'
  let p : Fin t → J → Fin (k + 1) := fun q => p' q.castSucc
  let z : J → Fin (k + 1) := p' (Fin.last t)
  have hp : dhjAppend p z = p' := by
    funext q
    refine Fin.lastCases ?_ (fun r => ?_) q
    · exact Fin.lastCases_last
    · exact Fin.lastCases_castSucc r
  rw [← hp, dhjJoinAt_append h p z y, dhjJoinAt_append h p z y']
  have htail :
      dhjBlockCore i (dhjTailCons h z y) =
        dhjBlockCore i (dhjTailCons h z y') := by
    funext q j
    by_cases hq : q.val = 0
    · simp [dhjBlockCore, dhjTailCons, hq]
    · have heq := congrFun (congrFun hyy' ⟨q.val - 1, by omega⟩) j
      simpa [dhjBlockCore, dhjTailCons, hq] using heq
  have hRmem :
      dhjMiddleWord h p z y ∈ R ↔ dhjMiddleWord h p z y' ∈ R := by
    calc
      dhjMiddleWord h p z y ∈ R ↔
          dhjJoinAt (by omega) p (dhjTailCons h z y) ∈ R := by
        rw [dhjJoinAt_tailCons]
      _ ↔ dhjJoinAt (by omega) p (dhjTailCons h z y') ∈ R :=
        hR p _ _ htail
      _ ↔ dhjMiddleWord h p z y' ∈ R := by
        rw [dhjJoinAt_tailCons]
  have hBmem (u : Fin (Q - (t + 1)) → J → Fin (k + 1)) :
      dhjMiddleWord h p z u ∈ dhjBatch h S V ↔
        (p, u) ∈ S ∧ z ∈ dhjSubspacePoints V := by
    rw [dhj_mem_batch]
    change
      (dhjMiddleEquiv h ((dhjMiddleEquiv h).symm ((p, u), z))).1 ∈ S ∧
          (dhjMiddleEquiv h ((dhjMiddleEquiv h).symm ((p, u), z))).2 ∈
            dhjSubspacePoints V ↔ _
    simp
  simp only [Finset.mem_sdiff]
  rw [hRmem, hBmem y, hBmem y', hS p y y' hyy']

private noncomputable def dhjFlatSet {k Q : ℕ} {J : Type*}
    (C : Finset (Fin Q → J → Fin (k + 1))) :
    Finset (Fin Q × J → Fin (k + 1)) := by
  classical
  exact C.map (dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))).toEmbedding

private theorem dhjFlatSet_union {k Q : ℕ} {J : Type*}
    [DecidableEq (Fin Q → J → Fin (k + 1))]
    [DecidableEq (Fin Q × J → Fin (k + 1))]
    (C B : Finset (Fin Q → J → Fin (k + 1))) :
    dhjFlatSet (C ∪ B) = dhjFlatSet C ∪ dhjFlatSet B := by
  exact Finset.map_union C B

private theorem dhjFlatSet_batch {k d Q t : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))] (h : t + 1 ≤ Q)
    (S : Finset ((Fin t → J → Fin (k + 1)) ×
      (Fin (Q - (t + 1)) → J → Fin (k + 1))))
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjFlatSet (dhjBatch h S V) = dhjFlatBatch h S V := by
  rfl

private theorem dhjTiled_union {k d : ℕ} {I : Type*}
    [DecidableEq (I → Fin (k + 1))]
    {C B : Finset (I → Fin (k + 1))}
    (hC : dhjTiled d k C) (hB : dhjTiled d k B) (hCB : Disjoint C B) :
    dhjTiled d k (C ∪ B) := by
  induction hB generalizing C with
  | empty => simpa using hC
  | add D V hD hDV ih =>
      have hCD : Disjoint C D := (Finset.disjoint_union_right.mp hCB).1
      have hCV : Disjoint C (dhjSubspacePoints V) :=
        (Finset.disjoint_union_right.mp hCB).2
      have hCDtiled : dhjTiled d k (C ∪ D) := ih hC hCD
      have hdis : Disjoint (C ∪ D) (dhjSubspacePoints V) :=
        Finset.disjoint_union_left.mpr ⟨hCV, hDV⟩
      have hadd := dhjTiled.add (C ∪ D) V hCDtiled hdis
      simpa only [Finset.union_assoc] using hadd

private theorem dhjDensity_union {X : Type*} [Fintype X]
    [DecidableEq X]
    (A B : Finset X) (hAB : Disjoint A B) :
    dhjDensity (A ∪ B) = dhjDensity A + dhjDensity B := by
  simp only [dhjDensity, Finset.card_union_of_disjoint hAB, Nat.cast_add, add_div]

private theorem dhjDensity_subspacePoints {k d : ℕ} {J : Type*}
    [Fintype (J → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) :
    dhjDensity (dhjSubspacePoints V) =
      ((k + 1 : ℕ) : ℝ) ^ d / Fintype.card (J → Fin (k + 1)) := by
  rw [dhjDensity, dhj_card_subspacePoints]
  simp only [Fintype.card_fin, Nat.cast_pow]

private noncomputable def dhjTileGain (k d : ℕ) {J : Type*}
    [Fintype J] [Fintype (J → Fin (k + 1))] (β : ℝ) : ℝ :=
  β / Fintype.card (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) *
    (((k + 1 : ℕ) : ℝ) ^ d / Fintype.card (J → Fin (k + 1)))

private theorem dhj_tiling_iteration {k d Q : ℕ} {J : Type*}
    [Fintype J] [Fintype (J → Fin (k + 1))]
    (i : Fin k) {β : ℝ} (hβ : 0 < β) (hβle : β ≤ 1)
    (hRestr : ∀ E : Finset (J → Fin (k + 1)), β ≤ dhjDensity E →
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J,
        ∀ x : Fin d → Fin k, V (Fin.castSucc ∘ x) ∈ E)
    (D : Finset (Fin Q → J → Fin (k + 1)))
    (hD : dhjBlockInsensitive i D) :
    ∀ t : ℕ, ∀ ht : t ≤ Q,
      ∃ C R : Finset (Fin Q → J → Fin (k + 1)),
        C ∪ R = D ∧ Disjoint C R ∧ dhjTiled d k (dhjFlatSet C) ∧
          (dhjDensity R < 2 * β ∨
            2 * β ≤ dhjDensity R ∧
              (t : ℝ) * dhjTileGain k d (J := J) β ≤ dhjDensity C ∧
              dhjStageInsensitive (t := t) i R ht) := by
  intro t ht
  induction t with
  | zero =>
      refine ⟨∅, D, by simp, Finset.disjoint_empty_left D, ?_, ?_⟩
      · have hflat : dhjFlatSet (∅ : Finset (Fin Q → J → Fin (k + 1))) = ∅ := by
          simp [dhjFlatSet]
        rw [hflat]
        exact dhjTiled.empty
      · by_cases hlow : dhjDensity D < 2 * β
        · exact Or.inl hlow
        · refine Or.inr ⟨le_of_not_gt hlow, ?_, dhjStageInsensitive_zero i D hD⟩
          simp
  | succ t ih =>
      obtain ⟨C, R, hpart, hdis, htile, hstate⟩ := ih (by omega)
      rcases hstate with hlow | ⟨hRden, hCden, hRins⟩
      · exact ⟨C, R, hpart, hdis, htile, Or.inl hlow⟩
      · let hstep : t + 1 ≤ Q := by omega
        obtain ⟨V, S, hSden, hSin, hSins⟩ :=
          dhj_tiling_step_data i hstep hβ hβle hRestr R hRden hRins
        let B := dhjBatch (J := J) hstep S V
        have hBsub : B ⊆ R := dhjBatch_subset hstep R S V hSin
        have hCB : Disjoint C B := by
          rw [Finset.disjoint_left]
          intro x hxC hxB
          exact (Finset.disjoint_left.mp hdis) hxC (hBsub hxB)
        have hpart' : (C ∪ B) ∪ (R \ B) = D := by
          ext x
          have hxpart : (x ∈ C ∨ x ∈ R) ↔ x ∈ D := by
            have := Finset.ext_iff.mp hpart x
            simpa only [Finset.mem_union] using this
          simp only [Finset.mem_union, Finset.mem_sdiff]
          rw [← hxpart]
          constructor
          · rintro ((hxC | hxB) | ⟨hxR, _⟩)
            · exact Or.inl hxC
            · exact Or.inr (hBsub hxB)
            · exact Or.inr hxR
          · rintro (hxC | hxR)
            · exact Or.inl (Or.inl hxC)
            · by_cases hxB : x ∈ B
              · exact Or.inl (Or.inr hxB)
              · exact Or.inr ⟨hxR, hxB⟩
        have hdis' : Disjoint (C ∪ B) (R \ B) := by
          rw [Finset.disjoint_left]
          intro x hxCB hxR
          simp only [Finset.mem_union] at hxCB
          simp only [Finset.mem_sdiff] at hxR
          rcases hxCB with hxC | hxB
          · exact (Finset.disjoint_left.mp hdis) hxC hxR.1
          · exact hxR.2 hxB
        have htileB : dhjTiled d k (dhjFlatSet B) := by
          rw [dhjFlatSet_batch]
          exact dhjTiled_flatBatch hstep S V
        have hflatDis : Disjoint (dhjFlatSet C) (dhjFlatSet B) := by
          exact (Finset.disjoint_map _).mpr hCB
        have htile' : dhjTiled d k (dhjFlatSet (C ∪ B)) := by
          have hu := dhjTiled_union htile htileB hflatDis
          convert hu using 1
          exact dhjFlatSet_union C B
        have hBden : dhjTileGain k d (J := J) β ≤ dhjDensity B := by
          calc
            dhjTileGain k d (J := J) β =
                (β / Fintype.card
                  (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J)) *
                  dhjDensity (dhjSubspacePoints V) := by
              rw [dhjDensity_subspacePoints]
              rfl
            _ ≤ dhjDensity S * dhjDensity (dhjSubspacePoints V) := by
              exact mul_le_mul_of_nonneg_right hSden
                (dhjDensity_nonneg (dhjSubspacePoints V))
            _ = dhjDensity (dhjBatch (J := J) hstep S V) := by
              rw [dhjDensity_batch]
            _ = dhjDensity B := rfl
        have hCden' :
            ((t + 1 : ℕ) : ℝ) * dhjTileGain k d (J := J) β ≤
              dhjDensity (C ∪ B) := by
          calc
            ((t + 1 : ℕ) : ℝ) * dhjTileGain k d (J := J) β =
                (t : ℝ) * dhjTileGain k d (J := J) β +
                  dhjTileGain k d (J := J) β := by
              push_cast
              ring
            _ ≤ dhjDensity C + dhjDensity B := add_le_add hCden hBden
            _ = dhjDensity (C ∪ B) := (dhjDensity_union C B hCB).symm
        have hRins' :
            dhjStageInsensitive (t := t + 1) i (R \ B) (by omega) := by
          change dhjStageInsensitive (t := t + 1) i
            (R \ dhjBatch (J := J) hstep S V) hstep
          exact dhjStageInsensitive_sdiff_batch i hstep R hRins S hSins V
        by_cases hlow' : dhjDensity (R \ B) < 2 * β
        · exact ⟨C ∪ B, R \ B, hpart', hdis', htile', Or.inl hlow'⟩
        · exact ⟨C ∪ B, R \ B, hpart', hdis', htile',
            Or.inr ⟨le_of_not_gt hlow', hCden', hRins'⟩⟩

private theorem dhj_tiling_insensitive {k d : ℕ} {J : Type*}
    [Fintype J] [Fintype (J → Fin (k + 1))]
    {β : ℝ} (hβ : 0 < β) (hβle : β ≤ 1)
    (hRestr : ∀ E : Finset (J → Fin (k + 1)), β ≤ dhjDensity E →
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) J,
        ∀ x : Fin d → Fin k, V (Fin.castSucc ∘ x) ∈ E) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (i : Fin k)
      (D : Finset (Fin Q → J → Fin (k + 1))),
      dhjBlockInsensitive i D →
        ∃ C : Finset (Fin Q → J → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k (dhjFlatSet C) ∧
            dhjDensity (D \ C) < 2 * β := by
  let _ : Nonempty (J → Fin (k + 1)) := ⟨fun _ => 0⟩
  have huniv : β ≤ dhjDensity
      (Finset.univ : Finset (J → Fin (k + 1))) := by
    rw [dhjDensity_univ]
    exact hβle
  obtain ⟨V₀, hV₀⟩ := hRestr Finset.univ huniv
  let _ : Nonempty (Combinatorics.Subspace (Fin d) (Fin (k + 1)) J) := ⟨V₀⟩
  have hgain : 0 < dhjTileGain k d (J := J) β := by
    simp only [dhjTileGain]
    positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / dhjTileGain k d (J := J) β)
  have hQgain : 1 < (Q : ℝ) * dhjTileGain k d (J := J) β := by
    calc
      1 = (1 / dhjTileGain k d (J := J) β) *
          dhjTileGain k d (J := J) β :=
        (one_div_mul_cancel hgain.ne').symm
      _ < (Q : ℝ) * dhjTileGain k d (J := J) β :=
        mul_lt_mul_of_pos_right hQ hgain
  have hQpos : 0 < Q := by
    have hreal : (0 : ℝ) < Q := (by positivity : (0 : ℝ) < 1 /
      dhjTileGain k d (J := J) β).trans hQ
    exact_mod_cast hreal
  refine ⟨Q, hQpos, ?_⟩
  intro i D hD
  obtain ⟨C, R, hpart, hdis, htile, hstate⟩ :=
    dhj_tiling_iteration i hβ hβle hRestr D hD Q le_rfl
  have hCsub : C ⊆ D := by
    intro x hx
    rw [← hpart]
    exact Finset.mem_union_left R hx
  have hres : D \ C = R := by
    ext x
    have hdisx := Finset.disjoint_left.mp hdis
    have hxpart : (x ∈ C ∨ x ∈ R) ↔ x ∈ D := by
      have := Finset.ext_iff.mp hpart x
      simpa only [Finset.mem_union] using this
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxD, hxC⟩
      exact (hxpart.mpr hxD).resolve_left hxC
    · intro hxR
      refine ⟨hxpart.mp (Or.inr hxR), ?_⟩
      exact fun hxC => hdisx hxC hxR
  rcases hstate with hlow | ⟨_, hCden, _⟩
  · refine ⟨C, hCsub, htile, ?_⟩
    rwa [hres]
  · have hCle : dhjDensity C ≤ 1 := dhjDensity_le_one C
    exfalso
    exact (not_lt_of_ge (hCden.trans hCle)) hQgain

private def dhjWordEquiv {I I' α : Type*} (e : I ≃ I') :
    (I → α) ≃ (I' → α) :=
  Equiv.arrowCongr e (Equiv.refl α)

private theorem dhj_mem_map_equiv {X Y : Type*} (e : X ≃ Y)
    (A : Finset X) (y : Y) :
    y ∈ A.map e.toEmbedding ↔ e.symm y ∈ A := by
  classical
  simp

private theorem dhjWordEquiv_replaceLast {k : ℕ} {I I' : Type*}
    (i : Fin k) (e : I ≃ I') (w : I → Fin (k + 1)) :
    dhjWordEquiv e (dhjReplaceLast i w) =
      dhjReplaceLast i (dhjWordEquiv e w) := by
  rfl

private theorem dhjInsensitive.map_wordEquiv {k : ℕ} {I I' : Type*}
    (i : Fin k) (e : I ≃ I') (D : Finset (I → Fin (k + 1)))
    (hD : dhjInsensitive i D) :
    dhjInsensitive i (D.map (dhjWordEquiv e).toEmbedding) := by
  intro w
  rw [dhj_mem_map_equiv, dhj_mem_map_equiv]
  change (dhjWordEquiv e).symm w ∈ D ↔
    dhjReplaceLast i ((dhjWordEquiv e).symm w) ∈ D
  exact hD ((dhjWordEquiv e).symm w)

private theorem dhjSubspace_reindex_apply {d k : ℕ} {I I' : Type*}
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) I)
    (e : I ≃ I') (z : Fin d → Fin (k + 1)) :
    V.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin (k + 1))) e z =
      dhjWordEquiv e (V z) := by
  funext q
  simp [dhjWordEquiv]

private theorem dhjSubspacePoints_reindex {d k : ℕ} {I I' : Type*}
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) I) (e : I ≃ I') :
    (dhjSubspacePoints V).map (dhjWordEquiv e).toEmbedding =
      dhjSubspacePoints
        (V.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin (k + 1))) e) := by
  classical
  ext w
  rw [dhj_mem_map_equiv, dhj_mem_subspacePoints, dhj_mem_subspacePoints]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [dhjSubspace_reindex_apply, hz, Equiv.apply_symm_apply]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply (dhjWordEquiv e).injective
    rw [Equiv.apply_symm_apply, ← dhjSubspace_reindex_apply, hz]

private theorem dhjTiled.map_wordEquiv {d k : ℕ} {I I' : Type*}
    [DecidableEq (I → Fin (k + 1))] [DecidableEq (I' → Fin (k + 1))]
    (e : I ≃ I') {C : Finset (I → Fin (k + 1))} (hC : dhjTiled d k C) :
    dhjTiled d k (C.map (dhjWordEquiv e).toEmbedding) := by
  induction hC with
  | empty => simpa using (dhjTiled.empty : dhjTiled d k
      (∅ : Finset (I' → Fin (k + 1))))
  | add C V hC hdis ih =>
      let V' := V.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin (k + 1))) e
      have hdis' : Disjoint
          (C.map (dhjWordEquiv e).toEmbedding) (dhjSubspacePoints V') := by
        rw [← dhjSubspacePoints_reindex V e]
        exact (Finset.disjoint_map _).mpr hdis
      have hadd := dhjTiled.add (C.map (dhjWordEquiv e).toEmbedding) V' ih hdis'
      rw [Finset.map_union, dhjSubspacePoints_reindex V e]
      exact hadd

private theorem dhj_exists_tiling_insensitive_fin {k d : ℕ} {β : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hβ : 0 < β) (hβle : β ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ (i : Fin k) (D : Finset (Fin n → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin n → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β := by
  classical
  obtain ⟨P, R, hP, hRestr⟩ :=
    dhj_exists_restricted_subspace_type hk hd hβ hβle hDHJ
  let J := Fin (R + 1) × Fin P
  obtain ⟨Q, hQpos, hQ⟩ :=
    dhj_tiling_insensitive hβ hβle (J := J) hRestr
  let I := Fin Q × J
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let b := dhjCurryEquiv (L := Q) (J := J) (α := Fin (k + 1))
  let w := dhjWordEquiv e ( α := Fin (k + 1))
  let f := b.trans w
  have hnpos : 0 < n := by
    apply Fintype.card_pos_iff.mpr
    let q : I := (⟨0, hQpos⟩, (⟨0, by omega⟩, ⟨0, hP⟩))
    exact ⟨q⟩
  refine ⟨n, hnpos, ?_⟩
  intro i D hD
  let Dflat := D.map w.symm.toEmbedding
  let Dblock := D.map f.symm.toEmbedding
  have hDflat : dhjInsensitive i Dflat := by
    dsimp only [Dflat, w]
    exact hD.map_wordEquiv i e.symm D
  have hDblockEq : Dblock = Dflat.map b.symm.toEmbedding := by
    ext u
    rw [dhj_mem_map_equiv, dhj_mem_map_equiv, dhj_mem_map_equiv]
    rfl
  have hDblock : dhjBlockInsensitive i Dblock := by
    rw [hDblockEq]
    exact dhjBlockInsensitive_map_flatten i Dflat hDflat
  obtain ⟨Cblock, hCsub, hCtile, hCsmall⟩ := hQ i Dblock hDblock
  let Cflat := dhjFlatSet Cblock
  let C := Cflat.map w.toEmbedding
  refine ⟨C, ?_, ?_, ?_⟩
  · have hflatSub : Cflat ⊆ Dflat := by
      intro x hx
      have hxb : b.symm x ∈ Cblock := by
        simpa [Cflat, dhjFlatSet] using hx
      have hxbD := hCsub hxb
      rw [hDblockEq, dhj_mem_map_equiv] at hxbD
      simpa using hxbD
    intro x hx
    have hxflat : w.symm x ∈ Cflat := by
      simpa [C] using hx
    have hxDflat := hflatSub hxflat
    dsimp only [Dflat] at hxDflat
    rw [dhj_mem_map_equiv] at hxDflat
    simpa using hxDflat
  · dsimp only [C]
    exact hCtile.map_wordEquiv e
  · have hres : D \ C = (Dblock \ Cblock).map f.toEmbedding := by
      have hDmap : Dblock.map f.toEmbedding = D := by
        ext x
        rw [dhj_mem_map_equiv, dhj_mem_map_equiv]
        simp
      have hCmap : Cblock.map f.toEmbedding = C := by
        ext x
        rw [dhj_mem_map_equiv]
        change f.symm x ∈ Cblock ↔ x ∈ Cflat.map w.toEmbedding
        rw [dhj_mem_map_equiv]
        change f.symm x ∈ Cblock ↔ w.symm x ∈ Cblock.map b.toEmbedding
        rw [dhj_mem_map_equiv]
        rfl
      rw [Finset.map_sdiff, hDmap, hCmap]
    rw [hres, dhjDensity_map_equiv]
    exact hCsmall

private theorem dhjInsensitive.pullback {k m : ℕ} {I : Type*}
    (i : Fin k) (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    dhjInsensitive i (dhjPullback V E) := by
  intro z
  simp only [dhj_mem_pullback]
  rw [hE (V z), hE (V (dhjReplaceLast i z))]
  rw [dhjSubspace_replaceLast]
  rfl

private theorem dhjSubspacePoints_comp {k m d : ℕ} {I : Type*}
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    (W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)) :
    (dhjSubspacePoints W).map ⟨V, dhjSubspace_apply_injective V⟩ =
      dhjSubspacePoints (V.comp W) := by
  classical
  ext x
  simp [dhjSubspacePoints, Combinatorics.Subspace.comp_apply]

private theorem dhjTiled.map_subspace {k m d : ℕ} {I : Type*}
    [DecidableEq (Fin m → Fin (k + 1))]
    [DecidableEq (I → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    {C : Finset (Fin m → Fin (k + 1))} (hC : dhjTiled d k C) :
    dhjTiled d k (C.map ⟨V, dhjSubspace_apply_injective V⟩) := by
  induction hC with
  | empty => simpa using (dhjTiled.empty :
      dhjTiled d k (∅ : Finset (I → Fin (k + 1))))
  | add C W hC hdis ih =>
      have hdis' : Disjoint
          (C.map ⟨V, dhjSubspace_apply_injective V⟩)
          (dhjSubspacePoints (V.comp W)) := by
        rw [← dhjSubspacePoints_comp V W]
        exact (Finset.disjoint_map _).mpr hdis
      have hadd := dhjTiled.add
        (C.map ⟨V, dhjSubspace_apply_injective V⟩) (V.comp W) ih hdis'
      rw [Finset.map_union, dhjSubspacePoints_comp V W]
      exact hadd

private theorem dhjDensity_map_subspace {k m : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    (A : Finset (Fin m → Fin (k + 1))) :
    dhjDensity (A.map ⟨V, dhjSubspace_apply_injective V⟩) =
      dhjDensity A * dhjDensity (dhjSubspacePoints V) := by
  rw [dhjDensity, dhjDensity, dhjDensity_subspacePoints]
  simp only [Finset.card_map, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hbase : (0 : ℝ) < (k + 1 : ℕ) ^ m := by positivity
  field_simp

private theorem dhj_refine_one_tile {k m d : ℕ} {I : Type*}
    [Fintype I] [Fintype (I → Fin (k + 1))]
    (i : Fin k) {β : ℝ}
    (hSingle : ∀ (D : Finset (Fin m → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin m → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β)
    (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    ∃ B : Finset (I → Fin (k + 1)),
      B ⊆ dhjSubspacePoints V ∩ E ∧ dhjTiled d k B ∧
        dhjDensity ((dhjSubspacePoints V ∩ E) \ B) ≤
          2 * β * dhjDensity (dhjSubspacePoints V) := by
  classical
  let EV := dhjPullback V E
  have hEV : dhjInsensitive i EV := hE.pullback i E V
  obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hSingle EV hEV
  let B := C.map ⟨V, dhjSubspace_apply_injective V⟩
  refine ⟨B, ?_, hCtile.map_subspace V, ?_⟩
  · intro x hx
    obtain ⟨z, hzC, rfl⟩ := Finset.mem_map.mp hx
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩
    · exact (dhj_mem_pullback V E z).mp (hCsub hzC)
  · have hres : (dhjSubspacePoints V ∩ E) \ B =
        (EV \ C).map ⟨V, dhjSubspace_apply_injective V⟩ := by
      ext x
      constructor
      · intro hx
        have hx' := Finset.mem_sdiff.mp hx
        obtain ⟨z, hz⟩ := (dhj_mem_subspacePoints V x).mp
          (Finset.mem_inter.mp hx'.1).1
        subst x
        apply Finset.mem_map.mpr
        refine ⟨z, ?_, rfl⟩
        rw [Finset.mem_sdiff]
        refine ⟨(dhj_mem_pullback V E z).mpr (Finset.mem_inter.mp hx'.1).2, ?_⟩
        intro hzC
        exact hx'.2 (Finset.mem_map.mpr ⟨z, hzC, rfl⟩)
      · intro hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
        have hz' := Finset.mem_sdiff.mp hz
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_inter.mpr ⟨?_, (dhj_mem_pullback V E z).mp hz'.1⟩, ?_⟩
        · exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩
        · intro hzB
          obtain ⟨z', hz'C, hz'eq⟩ := Finset.mem_map.mp hzB
          exact hz'.2 ((dhjSubspace_apply_injective V hz'eq) ▸ hz'C)
    rw [hres, dhjDensity_map_subspace]
    have hpos : 0 < dhjDensity (dhjSubspacePoints V) := by
      rw [dhjDensity_subspacePoints]
      positivity
    exact (mul_lt_mul_of_pos_right hCsmall hpos).le

private theorem dhj_refine_tiled {k m d : ℕ} {I : Type*}
    [Fintype I] [Fintype (I → Fin (k + 1))]
    (i : Fin k) {β : ℝ}
    (hSingle : ∀ (D : Finset (Fin m → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin m → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β)
    (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    {C : Finset (I → Fin (k + 1))} (hC : dhjTiled m k C) :
    ∃ B : Finset (I → Fin (k + 1)),
      B ⊆ C ∩ E ∧ dhjTiled d k B ∧
        dhjDensity ((C ∩ E) \ B) ≤ 2 * β * dhjDensity C := by
  induction hC with
  | empty =>
      refine ⟨∅, by simp, dhjTiled.empty, ?_⟩
      simp [dhjDensity_empty]
  | add C V hCtiled hdis ih =>
      obtain ⟨B₀, hB₀sub, hB₀tile, hB₀small⟩ := ih
      obtain ⟨Bᵥ, hBᵥsub, hBᵥtile, hBᵥsmall⟩ :=
        dhj_refine_one_tile i hSingle E hE V
      have hBdis : Disjoint B₀ Bᵥ := by
        rw [Finset.disjoint_left]
        intro x hx₀ hxᵥ
        exact (Finset.disjoint_left.mp hdis)
          (Finset.mem_inter.mp (hB₀sub hx₀)).1
          (Finset.mem_inter.mp (hBᵥsub hxᵥ)).1
      refine ⟨B₀ ∪ Bᵥ, ?_, dhjTiled_union hB₀tile hBᵥtile hBdis, ?_⟩
      · intro x hx
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hx with hx₀ | hxᵥ
          · have hx' := Finset.mem_inter.mp (hB₀sub hx₀)
            exact Finset.mem_union_left _ hx'.1
          · have hx' := Finset.mem_inter.mp (hBᵥsub hxᵥ)
            exact Finset.mem_union_right _ hx'.1
        · rcases Finset.mem_union.mp hx with hx₀ | hxᵥ
          · exact (Finset.mem_inter.mp (hB₀sub hx₀)).2
          · exact (Finset.mem_inter.mp (hBᵥsub hxᵥ)).2
      · let R₀ := (C ∩ E) \ B₀
        let Rᵥ := (dhjSubspacePoints V ∩ E) \ Bᵥ
        have hres : ((C ∪ dhjSubspacePoints V) ∩ E) \ (B₀ ∪ Bᵥ) = R₀ ∪ Rᵥ := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union,
            not_or, R₀, Rᵥ]
          constructor
          · rintro ⟨⟨hxC | hxV, hxE⟩, hxB₀, hxBᵥ⟩
            · exact Or.inl ⟨⟨hxC, hxE⟩, hxB₀⟩
            · exact Or.inr ⟨⟨hxV, hxE⟩, hxBᵥ⟩
          · rintro (⟨⟨hxC, hxE⟩, hxB₀⟩ | ⟨⟨hxV, hxE⟩, hxBᵥ⟩)
            · refine ⟨⟨Or.inl hxC, hxE⟩, hxB₀, ?_⟩
              intro hxBᵥ
              exact (Finset.disjoint_left.mp hdis) hxC
                (Finset.mem_inter.mp (hBᵥsub hxBᵥ)).1
            · refine ⟨⟨Or.inr hxV, hxE⟩, ?_, hxBᵥ⟩
              intro hxB₀
              exact (Finset.disjoint_left.mp hdis)
                (Finset.mem_inter.mp (hB₀sub hxB₀)).1 hxV
        have hRdis : Disjoint R₀ Rᵥ := by
          rw [Finset.disjoint_left]
          intro x hx₀ hxᵥ
          exact (Finset.disjoint_left.mp hdis)
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx₀).1).1
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxᵥ).1).1
        rw [hres, dhjDensity_union R₀ Rᵥ hRdis,
          dhjDensity_union C (dhjSubspacePoints V) hdis]
        calc
          dhjDensity R₀ + dhjDensity Rᵥ ≤
              2 * β * dhjDensity C +
                2 * β * dhjDensity (dhjSubspacePoints V) :=
            add_le_add hB₀small hBᵥsmall
          _ = 2 * β *
              (dhjDensity C + dhjDensity (dhjSubspacePoints V)) := by ring

private noncomputable def dhjMeet {r k n : ℕ}
    (D : Fin r → Finset (Fin n → Fin (k + 1))) :
    Finset (Fin n → Fin (k + 1)) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, x ∈ D j

@[simp]
private theorem dhj_mem_meet {r k n : ℕ}
    (D : Fin r → Finset (Fin n → Fin (k + 1)))
    (x : Fin n → Fin (k + 1)) :
    x ∈ dhjMeet D ↔ ∀ j, x ∈ D j := by
  classical
  simp [dhjMeet]

private theorem dhjMeet_succ {r k n : ℕ}
    (D : Fin (r + 1) → Finset (Fin n → Fin (k + 1))) :
    dhjMeet D = dhjMeet (fun j : Fin r => D j.castSucc) ∩ D (Fin.last r) := by
  classical
  ext x
  simp only [dhj_mem_meet, Finset.mem_inter]
  exact Fin.forall_fin_succ'

private def dhjIdentitySubspace (d k : ℕ) :
    Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin d) where
  idxFun := Sum.inr
  proper j := ⟨j, rfl⟩

@[simp]
private theorem dhjIdentitySubspace_apply {d k : ℕ}
    (x : Fin d → Fin (k + 1)) : dhjIdentitySubspace d k x = x := by
  rfl

private theorem dhjSubspacePoints_identity {d k : ℕ} :
    dhjSubspacePoints (dhjIdentitySubspace d k) = Finset.univ := by
  classical
  ext x
  simp

private theorem dhj_exists_structured_tiling {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∀ r d : ℕ, 0 < d → ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ n : ℕ, ∀ (a : Fin r → Fin k)
        (D : Fin r → Finset (Fin n → Fin (k + 1))),
        (∀ j, dhjInsensitive (a j) (D j)) →
          ∃ C : Finset (Fin n → Fin (k + 1)),
            C ⊆ dhjMeet D ∧ dhjTiled d k C ∧
              dhjDensity (dhjMeet D \ C) ≤ 2 * (r : ℝ) * β := by
  intro r
  induction r with
  | zero =>
      intro d hd β hβ hβle
      refine ⟨d, ?_⟩
      intro a D hD
      have hmeet : dhjMeet D = Finset.univ := by
        ext x
        simp
      have htile : dhjTiled d k
          (Finset.univ : Finset (Fin d → Fin (k + 1))) := by
        have hadd := dhjTiled.add
          (∅ : Finset (Fin d → Fin (k + 1))) (dhjIdentitySubspace d k)
          (dhjTiled.empty : dhjTiled d k
            (∅ : Finset (Fin d → Fin (k + 1))))
          (Finset.disjoint_empty_left _)
        simpa [dhjSubspacePoints_identity] using hadd
      refine ⟨Finset.univ, by simp [hmeet], htile, ?_⟩
      simp [hmeet, dhjDensity_empty]
  | succ r ih =>
      intro d hd β hβ hβle
      obtain ⟨m, hm, hSingle⟩ :=
        dhj_exists_tiling_insensitive_fin hk hd hβ hβle hDHJ
      obtain ⟨n, hOuter⟩ := ih m hm β hβ hβle
      refine ⟨n, ?_⟩
      intro a D hD
      let a₀ : Fin r → Fin k := fun j => a j.castSucc
      let D₀ : Fin r → Finset (Fin n → Fin (k + 1)) := fun j => D j.castSucc
      have hD₀ : ∀ j, dhjInsensitive (a₀ j) (D₀ j) := fun j => hD j.castSucc
      obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hOuter a₀ D₀ hD₀
      let i := a (Fin.last r)
      let E := D (Fin.last r)
      have hE : dhjInsensitive i E := hD (Fin.last r)
      obtain ⟨B, hBsub, hBtile, hBsmall⟩ :=
        dhj_refine_tiled i (hSingle i) E hE hCtile
      have hmeet : dhjMeet D = dhjMeet D₀ ∩ E := by
        simpa [D₀, E] using dhjMeet_succ D
      refine ⟨B, ?_, hBtile, ?_⟩
      · intro x hx
        rw [hmeet]
        have hx' := Finset.mem_inter.mp (hBsub hx)
        exact Finset.mem_inter.mpr ⟨hCsub hx'.1, hx'.2⟩
      · let M := dhjMeet D₀ ∩ E
        let X := M \ C
        let Y := (C ∩ E) \ B
        have hres : dhjMeet D \ B = X ∪ Y := by
          rw [hmeet]
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, X, Y, M]
          constructor
          · rintro ⟨hxM, hxB⟩
            by_cases hxC : x ∈ C
            · exact Or.inr ⟨⟨hxC, hxM.2⟩, hxB⟩
            · exact Or.inl ⟨hxM, hxC⟩
          · rintro (⟨hxM, hxC⟩ | ⟨⟨hxC, hxE'⟩, hxB⟩)
            · refine ⟨hxM, ?_⟩
              intro hxB
              exact hxC (Finset.mem_inter.mp (hBsub hxB)).1
            · exact ⟨⟨hCsub hxC, hxE'⟩, hxB⟩
        have hXY : Disjoint X Y := by
          rw [Finset.disjoint_left]
          intro x hxX hxY
          exact (Finset.mem_sdiff.mp hxX).2
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxY).1).1
        have hXsub : X ⊆ dhjMeet D₀ \ C := by
          intro x hx
          have hx' := Finset.mem_sdiff.mp hx
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx'.1).1, hx'.2⟩
        have hXsmall : dhjDensity X ≤ 2 * (r : ℝ) * β :=
          (dhjDensity_mono hXsub).trans hCsmall
        have hYsmall : dhjDensity Y ≤ 2 * β := by
          calc
            dhjDensity Y ≤ 2 * β * dhjDensity C := hBsmall
            _ ≤ 2 * β * 1 := by
              exact mul_le_mul_of_nonneg_left (dhjDensity_le_one C) (by positivity)
            _ = 2 * β := by ring
        rw [hres, dhjDensity_union X Y hXY]
        calc
          dhjDensity X + dhjDensity Y ≤ 2 * (r : ℝ) * β + 2 * β :=
            add_le_add hXsmall hYsmall
          _ = 2 * ((r + 1 : ℕ) : ℝ) * β := by
            push_cast
            ring

private theorem dhj_subspace_dimension_le {d n k : ℕ}
    (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n)) : d ≤ n := by
  classical
  let f : Fin d → Fin n := fun j => Classical.choose (V.proper j)
  have hf (j : Fin d) : V.idxFun (f j) = Sum.inr j :=
    Classical.choose_spec (V.proper j)
  have hfinj : Function.Injective f := by
    intro i j hij
    have h := (hf i).symm.trans ((congrArg V.idxFun hij).trans (hf j))
    exact Sum.inr.inj h
  simpa using Fintype.card_le_of_injective f hfinj

private theorem dhjTiled.dimension_le_of_nonempty {d n k : ℕ}
    {C : Finset (Fin n → Fin (k + 1))} (hC : dhjTiled d k C)
    (hCne : C.Nonempty) : d ≤ n := by
  induction hC with
  | empty => simp at hCne
  | add C V hC hdis ih => exact dhj_subspace_dimension_le V

private theorem dhj_inter_subspacePoints {k m : ℕ} {I : Type*}
    [DecidableEq (I → Fin (k + 1))]
    (A : Finset (I → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    A ∩ dhjSubspacePoints V =
      (dhjPullback V A).map ⟨V, dhjSubspace_apply_injective V⟩ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (dhj_mem_subspacePoints V x).mp
      (Finset.mem_inter.mp hx).2
    exact Finset.mem_map.mpr
      ⟨z, (dhj_mem_pullback V A z).mpr (Finset.mem_inter.mp hx).1, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_inter.mpr
      ⟨(dhj_mem_pullback V A z).mp hz,
        (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩⟩

private theorem dhjDensity_inter_subspacePoints {k m : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))] [DecidableEq (I → Fin (k + 1))]
    (A : Finset (I → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    dhjDensity (A ∩ dhjSubspacePoints V) =
      dhjDensityOn A V * dhjDensity (dhjSubspacePoints V) := by
  rw [dhj_inter_subspacePoints A V, dhjDensity_map_subspace]
  rfl

private theorem dhjTiled.exists_densityOn_ge {k d : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))]
    [DecidableEq (I → Fin (k + 1))]
    {C : Finset (I → Fin (k + 1))} (hC : dhjTiled d k C)
    (A : Finset (I → Fin (k + 1))) {q : ℝ} (hCne : C.Nonempty)
    (havg : q * dhjDensity C ≤ dhjDensity (A ∩ C)) :
    ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) I,
      dhjSubspacePoints V ⊆ C ∧ q ≤ dhjDensityOn A V := by
  induction hC with
  | empty => simp at hCne
  | add C V hCtiled hdis ih =>
      by_cases hV : q ≤ dhjDensityOn A V
      · refine ⟨V, ?_, hV⟩
        exact Finset.subset_union_right
      · have hAdis : Disjoint (A ∩ C) (A ∩ dhjSubspacePoints V) := by
          rw [Finset.disjoint_left]
          intro x hxC hxV
          exact (Finset.disjoint_left.mp hdis)
            (Finset.mem_inter.mp hxC).2 (Finset.mem_inter.mp hxV).2
        have hAunion : A ∩ (C ∪ dhjSubspacePoints V) =
            (A ∩ C) ∪ (A ∩ dhjSubspacePoints V) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          aesop
        have htotal : q *
              (dhjDensity C + dhjDensity (dhjSubspacePoints V)) ≤
            dhjDensity (A ∩ C) +
              dhjDensity (A ∩ dhjSubspacePoints V) := by
          rw [← dhjDensity_union C (dhjSubspacePoints V) hdis,
            ← dhjDensity_union (A ∩ C) (A ∩ dhjSubspacePoints V) hAdis,
            ← hAunion]
          exact havg
        have hVpos : 0 < dhjDensity (dhjSubspacePoints V) := by
          rw [dhjDensity_subspacePoints]
          positivity
        have hVsmall : dhjDensity (A ∩ dhjSubspacePoints V) <
            q * dhjDensity (dhjSubspacePoints V) := by
          rw [dhjDensity_inter_subspacePoints A V]
          exact mul_lt_mul_of_pos_right (lt_of_not_ge hV) hVpos
        have hprev : q * dhjDensity C < dhjDensity (A ∩ C) := by
          nlinarith
        have hCne' : C.Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty.mp h, dhjDensity_empty] at hprev
          simp [dhjDensity_empty] at hprev
        obtain ⟨W, hWsub, hWden⟩ := ih hCne' hprev.le
        exact ⟨W, hWsub.trans Finset.subset_union_left, hWden⟩

private def dhjPrefixSubspace {I J α : Type*} (x : I → α) :
    Combinatorics.Subspace J α (I ⊕ J) where
  idxFun
    | Sum.inl i => Sum.inl (x i)
    | Sum.inr j => Sum.inr j
  proper j := ⟨Sum.inr j, rfl⟩

@[simp]
private theorem dhjPrefixSubspace_apply {I J α : Type*} (x : I → α)
    (z : J → α) : dhjPrefixSubspace x z = dhjConcat x z := by
  ext q
  cases q <;> rfl

private theorem dhj_exists_subspace_density_ge {k d m : ℕ} (hdm : d ≤ m)
    (A : Finset (Fin m → Fin (k + 1))) :
    ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m),
      dhjDensity A ≤ dhjDensityOn A V := by
  classical
  let t := m - d
  have hadd : t + d = m := Nat.sub_add_cancel hdm
  let e : Fin t ⊕ Fin d ≃ Fin m := finSumFinEquiv.trans (finCongr hadd)
  let w := dhjWordEquiv e.symm ( α := Fin (k + 1))
  let A' : Finset (Fin t ⊕ Fin d → Fin (k + 1)) := A.map w.toEmbedding
  have hAdens : dhjDensity A' = dhjDensity A := dhjDensity_map_equiv w A
  have havg : dhjDensity A ≤ Finset.expect Finset.univ
      (fun x : Fin t → Fin (k + 1) => dhjDensity (dhjSection A' x)) := by
    rw [← dhj_density_eq_expect_sections A', hAdens]
  obtain ⟨x, hxuniv, hx⟩ :=
    Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  let U : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin t ⊕ Fin d) :=
    dhjPrefixSubspace x
  let V := U.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin (k + 1))) e
  refine ⟨V, ?_⟩
  have hpull : dhjPullback V A = dhjSection A' x := by
    ext z
    rw [dhj_mem_pullback]
    simp only [dhjSection, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dhj_mem_map_equiv]
    have heq : w (V z) = dhjConcat x z := by
      calc
        w (V z) = U z := by
          funext q
          simp [w, V, dhjWordEquiv]
        _ = dhjConcat x z := dhjPrefixSubspace_apply x z
    rw [← heq, Equiv.symm_apply_apply]
  simpa [dhjDensityOn, hpull] using hx

private theorem dhjMeet_eq_familyMeet {k n : ℕ}
    (D : Fin k → Finset (Fin n → Fin (k + 1))) :
    dhjMeet D = dhjFamilyMeet D := by
  classical
  ext x
  simp

private theorem dhj_exists_family_tiling {k d : ℕ} {β : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hβ : 0 < β) (hβle : β ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ n : ℕ, ∀ (D : Fin k → Finset (Fin n → Fin (k + 1))),
      (∀ i, dhjInsensitive i (D i)) →
        ∃ C : Finset (Fin n → Fin (k + 1)),
          C ⊆ dhjFamilyMeet D ∧ dhjTiled d k C ∧
            dhjDensity (dhjFamilyMeet D \ C) ≤ 2 * (k : ℝ) * β := by
  obtain ⟨n, hn⟩ := dhj_exists_structured_tiling hk hDHJ k d hd β hβ hβle
  refine ⟨n, ?_⟩
  intro D hD
  obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hn (fun i => i) D hD
  rw [dhjMeet_eq_familyMeet] at hCsub hCsmall
  exact ⟨C, hCsub, hCtile, hCsmall⟩

private theorem dhj_correlation_after_tiling {X : Type*}
    [Fintype X] [Nonempty X] [DecidableEq X]
    {A D C : Finset X} {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (hCsub : C ⊆ D) (hDmass : γ ≤ dhjDensity D)
    (hrem : dhjDensity (D \ C) ≤ γ ^ 2 / 2)
    (hcorr : (δ + γ) * dhjDensity D ≤ dhjDensity (A ∩ D)) :
    (δ + γ / 2) * dhjDensity C ≤ dhjDensity (A ∩ C) := by
  let R := D \ C
  let S := (A ∩ D) \ (A ∩ C)
  have hDsum : dhjDensity R + dhjDensity C = dhjDensity D := by
    exact dhjDensity_sdiff_add hCsub
  have hACsub : A ∩ C ⊆ A ∩ D := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx).1, hCsub (Finset.mem_inter.mp hx).2⟩
  have hAsum : dhjDensity S + dhjDensity (A ∩ C) =
      dhjDensity (A ∩ D) := dhjDensity_sdiff_add hACsub
  have hSsub : S ⊆ R := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxAD := Finset.mem_inter.mp hx'.1
    exact Finset.mem_sdiff.mpr ⟨hxAD.2, fun hxC =>
      hx'.2 (Finset.mem_inter.mpr ⟨hxAD.1, hxC⟩)⟩
  have hSle : dhjDensity S ≤ dhjDensity R := dhjDensity_mono hSsub
  have hγD : 0 ≤ (γ / 2) * (dhjDensity D - γ) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hDmass)
  have hcoefR : 0 ≤ (δ + γ / 2) * dhjDensity R :=
    mul_nonneg (by positivity) (dhjDensity_nonneg R)
  dsimp only [R] at hDsum hrem hcoefR
  dsimp only [S] at hAsum hSle
  nlinarith

private theorem dhj_dichotomy_blocks {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 →
      ∀ d : ℕ, 0 < d → ∃ G R : ℕ, 0 < G ∧
      ∀ A : Finset (Fin (R + 1) → Fin G → Fin (k + 1)),
        ρ ≤ dhjDensity A →
          let A' := A.map (dhjFlattenEquiv (L := R + 1) (G := G)
            (α := Fin (k + 1))).toEmbedding
          (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin (R + 1) × Fin G),
              dhjLineIn A' l) ∨
            ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1))
                (Fin (R + 1) × Fin G),
              ρ + γ / 2 ≤ dhjDensityOn A' V := by
  classical
  obtain ⟨N₀, hN₀⟩ := hDHJ (δ / 4) (by positivity)
  let m₀ := N₀ + 1
  have hm₀ : 0 < m₀ := by simp [m₀]
  have hAt : dhjAt k m₀ (δ / 4) := hN₀ m₀ (by simp [m₀])
  obtain ⟨hθpos, hθle, hηpos, hηlt, hηsq, hγpos, hγle⟩ :=
    dhj_constants hk hm₀ hδ hδle
  let γ := dhjGamma k m₀ δ
  let η := dhjEta k m₀ δ
  have hηleone : η ≤ 1 := by
    dsimp only [η]
    linarith
  have hηsqle : η ^ 2 ≤ η := by
    nlinarith [mul_nonneg hηpos.le (sub_nonneg.mpr hηleone)]
  have hγleone : γ ≤ 1 := by
    dsimp only [γ, η] at hγle ⊢
    nlinarith
  have hγsqhalf_lt_one : γ ^ 2 / 2 < 1 := by
    nlinarith [mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  have hγsqhalf_lt_gamma : γ ^ 2 / 2 < γ := by
    nlinarith [mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  let β := γ ^ 2 / (4 * (k : ℝ))
  have hβpos : 0 < β := by dsimp only [β]; positivity
  have hβle : β ≤ 1 := by
    dsimp only [β]
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * k)]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg γ,
      mul_nonneg hγpos.le (sub_nonneg.mpr hγleone)]
  have herr : 2 * (k : ℝ) * β = γ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  refine ⟨γ, hγpos, ?_⟩
  intro ρ hδρ hρle
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hAtρ : dhjAt k m₀ (ρ / 4) := by
    intro A hA
    exact hAt A (by linarith)
  obtain ⟨hθρpos, hθρle, hηρpos, hηρlt, hηρsq, hγρpos, hγρle⟩ :=
    dhj_constants hk hm₀ hρ hρle
  let ηρ := dhjEta k m₀ ρ
  let γρ := dhjGamma k m₀ ρ
  have hθmono : dhjTheta k m₀ δ ≤ dhjTheta k m₀ ρ := by
    simp only [dhjTheta]
    gcongr
  have hηmono : η ≤ ηρ := by
    simp only [η, ηρ, dhjEta]
    gcongr
  have hγmono : γ ≤ γρ := by
    simp only [γ, γρ, dhjGamma]
    gcongr
  have hηρleone : ηρ ≤ 1 := by
    dsimp only [ηρ]
    linarith
  have hηρsqle : ηρ ^ 2 ≤ ηρ := by
    nlinarith [mul_nonneg hηρpos.le (sub_nonneg.mpr hηρleone)]
  have hγρleone : γρ ≤ 1 := by
    dsimp only [γρ, ηρ] at hγρle ⊢
    nlinarith
  have hγρsqhalf_lt : γρ ^ 2 / 2 < γρ := by
    nlinarith [mul_nonneg hγρpos.le (sub_nonneg.mpr hγρleone)]
  intro d hd
  obtain ⟨M₀, hkM₀, hratio⟩ :=
    dhj_exists_ratio_pow_le (by omega : 0 < k) hηpos
  let d' := max d (max M₀ m₀)
  have hd' : 0 < d' := hd.trans_le (le_max_left _ _)
  obtain ⟨m, hTile⟩ :=
    dhj_exists_family_tiling hk hd' hβpos hβle hDHJ
  let Dall : Fin k → Finset (Fin m → Fin (k + 1)) := fun _ => Finset.univ
  have hDall : ∀ i, dhjInsensitive i (Dall i) := fun i => dhjInsensitive_univ i
  obtain ⟨Call, hCallSub, hCallTile, hCallSmall⟩ := hTile Dall hDall
  have hmeetAll : dhjFamilyMeet Dall = Finset.univ := dhj_familyMeet_univ
  have hCallSmall' : dhjDensity (Finset.univ \ Call) ≤ γ ^ 2 / 2 := by
    rw [← herr, ← hmeetAll]
    exact hCallSmall
  have hCallNe : Call.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sdiff_empty,
      dhjDensity_univ] at hCallSmall'
    linarith
  have hd'm : d' ≤ m := hCallTile.dimension_le_of_nonempty hCallNe
  have hm₀m : m₀ ≤ m := by
    apply (le_max_right M₀ m₀).trans
    exact (le_max_right d (max M₀ m₀)).trans hd'm
  have hM₀m : M₀ ≤ m := by
    apply (le_max_left M₀ m₀).trans
    exact (le_max_right d (max M₀ m₀)).trans hd'm
  have hkm : k ≤ m := hkM₀.trans hM₀m
  have hratioM : ((k : ℝ) / (k + 1)) ^ m ≤ dhjEta k m₀ ρ :=
    (hratio m hM₀m).trans hηmono
  obtain ⟨G, R, hG, hCorr⟩ :=
    dhj_corollary11_blocks hk hm₀ hm₀m hkm hρ hρle hAtρ hratioM
  refine ⟨G, R, hG, ?_⟩
  intro A hA
  let A' := A.map (dhjFlattenEquiv (L := R + 1) (G := G)
    (α := Fin (k + 1))).toEmbedding
  by_cases hlineFree : dhjLineFree A'
  · right
    obtain ⟨W, D, hDi, hDmass, hDcorr⟩ := hCorr A hA hlineFree
    obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hTile D hDi
    have hCsmall' : dhjDensity (dhjFamilyMeet D \ C) ≤ γ ^ 2 / 2 := by
      rw [← herr]
      exact hCsmall
    have hCsmallρ : dhjDensity (dhjFamilyMeet D \ C) ≤ γρ ^ 2 / 2 := by
      calc
        dhjDensity (dhjFamilyMeet D \ C) ≤ γ ^ 2 / 2 := hCsmall'
        _ ≤ γρ ^ 2 / 2 := by
          exact div_le_div_of_nonneg_right
            ((sq_le_sq₀ hγpos.le hγρpos.le).2 hγmono) (by norm_num)
    let B := dhjPullback W A'
    have hCcorr : (ρ + γρ / 2) * dhjDensity C ≤ dhjDensity (B ∩ C) := by
      exact dhj_correlation_after_tiling hρ hγρpos hCsub hDmass hCsmallρ hDcorr
    have hCne : C.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sdiff_empty] at hCsmallρ
      exact (not_le_of_gt hγρsqhalf_lt) (hDmass.trans hCsmallρ)
    obtain ⟨V, hVsub, hVden⟩ :=
      hCtile.exists_densityOn_ge B hCne hCcorr
    let Z := W.comp V
    have hd_d' : d ≤ d' := le_max_left d (max M₀ m₀)
    obtain ⟨U, hUden⟩ :=
      dhj_exists_subspace_density_ge hd_d' (dhjPullback Z A')
    refine ⟨Z.comp U, ?_⟩
    calc
      ρ + γ / 2 ≤ ρ + γρ / 2 := by linarith
      _ ≤ dhjDensityOn B V := hVden
      _ = dhjDensityOn A' Z := (dhjDensityOn_comp A' W V).symm
      _ = dhjDensity (dhjPullback Z A') := rfl
      _ ≤ dhjDensityOn (dhjPullback Z A') U := hUden
      _ = dhjDensityOn A' (Z.comp U) := (dhjDensityOn_comp A' Z U).symm
  · left
    simpa only [dhjLineFree, not_forall, Classical.not_not] using hlineFree

private theorem dhj_dichotomy_fin {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 →
      ∀ d : ℕ, 0 < d → ∃ N : ℕ, 0 < N ∧
      ∀ A : Finset (Fin N → Fin (k + 1)), ρ ≤ dhjDensity A →
        (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin N), dhjLineIn A l) ∨
          ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin N),
            ρ + γ / 2 ≤ dhjDensityOn A V := by
  classical
  obtain ⟨γ, hγ, hblocks⟩ := dhj_dichotomy_blocks hk hδ hδle hDHJ
  refine ⟨γ, hγ, ?_⟩
  intro ρ hδρ hρle d hd
  obtain ⟨G, R, hG, hblock⟩ := hblocks ρ hδρ hρle d hd
  let I := Fin (R + 1) × Fin G
  let N := Fintype.card I
  let e : I ≃ Fin N := Fintype.equivFin I
  let b := dhjFlattenEquiv (L := R + 1) (G := G) (α := Fin (k + 1))
  let w := dhjWordEquiv e ( α := Fin (k + 1))
  let f := b.trans w
  have hN : 0 < N := by
    apply Fintype.card_pos_iff.mpr
    let q : I := (⟨0, by omega⟩, ⟨0, hG⟩)
    exact ⟨q⟩
  refine ⟨N, hN, ?_⟩
  intro A hA
  let Ablock := A.map f.symm.toEmbedding
  have hAblock : ρ ≤ dhjDensity Ablock := by
    rw [dhjDensity_map_equiv]
    exact hA
  obtain hline | hinc := hblock Ablock hAblock
  · left
    obtain ⟨l, hl⟩ := hline
    refine ⟨l.reindex e, ?_⟩
    intro a
    have ha := hl a
    change l a ∈ Ablock.map b.toEmbedding at ha
    rw [dhj_mem_map_equiv] at ha
    dsimp only [Ablock] at ha
    rw [dhj_mem_map_equiv] at ha
    have heq : l.reindex e a = w (l a) := by
      funext q
      change l.reindex e a q = l a (e.symm q)
      exact Combinatorics.Line.reindex_apply l e a q
    rw [heq]
    simpa [f] using ha
  · right
    obtain ⟨V, hV⟩ := hinc
    let V' := V.reindex (Equiv.refl (Fin d))
      (Equiv.refl (Fin (k + 1))) e
    refine ⟨V', ?_⟩
    have hpull : dhjPullback V' A = dhjPullback V
        (Ablock.map b.toEmbedding) := by
      ext z
      simp only [dhj_mem_pullback]
      rw [dhj_mem_map_equiv]
      dsimp only [Ablock]
      rw [dhj_mem_map_equiv]
      change V' z ∈ A ↔ f (b.symm (V z)) ∈ A
      have hVapply : V' z = w (V z) := dhjSubspace_reindex_apply V e z
      rw [hVapply]
      rfl
    simpa [dhjDensityOn, hpull] using hV

private theorem dhj_iterate_dichotomy {k : ℕ} {δ γ : ℝ}
    (_hδ : 0 < δ) (hγ : 0 < γ)
    (hstep : ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ d : ℕ, 0 < d →
      ∃ N : ℕ, 0 < N ∧ ∀ A : Finset (Fin N → Fin (k + 1)),
        ρ ≤ dhjDensity A →
          (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin N), dhjLineIn A l) ∨
            ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin N),
              ρ + γ / 2 ≤ dhjDensityOn A V) :
    ∀ r : ℕ, ∀ ρ : ℝ, δ ≤ ρ →
      1 < ρ + (r : ℝ) * (γ / 2) →
        ∃ N : ℕ, 0 < N ∧ dhjAt (k + 1) N ρ := by
  intro r
  induction r with
  | zero =>
      intro ρ hδρ htop
      refine ⟨1, by omega, ?_⟩
      intro A hA
      have hAle : dhjDensity A ≤ 1 := dhjDensity_le_one A
      exfalso
      norm_num at htop
      linarith
  | succ r ih =>
      intro ρ hδρ htop
      by_cases hρtop : 1 < ρ
      · refine ⟨1, by omega, ?_⟩
        intro A hA
        have hAle : dhjDensity A ≤ 1 := dhjDensity_le_one A
        exfalso
        linarith
      · have hρle : ρ ≤ 1 := le_of_not_gt hρtop
        have hnextTop : 1 < (ρ + γ / 2) + (r : ℝ) * (γ / 2) := by
          have heq : (ρ + γ / 2) + (r : ℝ) * (γ / 2) =
              ρ + ((r + 1 : ℕ) : ℝ) * (γ / 2) := by
            push_cast
            ring
          rw [heq]
          exact htop
        obtain ⟨d, hd, hcontinue⟩ :=
          ih (ρ + γ / 2) (by linarith) hnextTop
        obtain ⟨N, hN, hfirst⟩ := hstep ρ hδρ hρle d hd
        refine ⟨N, hN, ?_⟩
        intro A hA
        obtain ⟨l, hl⟩ | ⟨V, hV⟩ := hfirst A hA
        · exact ⟨l, hl⟩
        · obtain ⟨l, hl⟩ := hcontinue (dhjPullback V A) hV
          exact ⟨V.compLine l, (dhjLineIn_compLine_iff V A l).mpr hl⟩

private theorem dhjThreshold_succ {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε)
    {δ : ℝ} (hδ : 0 < δ) : dhjThreshold (k + 1) δ := by
  by_cases hδle : δ ≤ 1
  · obtain ⟨γ, hγ, hstep⟩ := dhj_dichotomy_fin hk hδ hδle hDHJ
    obtain ⟨r, hr⟩ := exists_nat_gt ((1 - δ) / (γ / 2))
    have hinc : 0 < γ / 2 := by positivity
    have htop : 1 < δ + (r : ℝ) * (γ / 2) := by
      have hmul := mul_lt_mul_of_pos_right hr hinc
      rw [div_mul_cancel₀ (1 - δ) hinc.ne'] at hmul
      linarith
    obtain ⟨N, hN, hAt⟩ :=
      dhj_iterate_dichotomy hδ hγ hstep r δ le_rfl htop
    exact dhjThreshold_of_at (by omega) hAt
  · refine ⟨1, ?_⟩
    intro n hn A hA
    have hAle : dhjDensity A ≤ 1 := dhjDensity_le_one A
    exfalso
    exact (not_le_of_gt (lt_of_not_ge hδle)) (hA.trans hAle)

private theorem dhjThreshold_add_two : ∀ t : ℕ, ∀ δ : ℝ, 0 < δ →
    dhjThreshold (t + 2) δ := by
  intro t
  induction t with
  | zero =>
      intro δ hδ
      simpa using dhjThreshold_two hδ
  | succ t ih =>
      intro δ hδ
      have h := dhjThreshold_succ (k := t + 2) (by omega)
        (fun ε hε => ih ε hε) hδ
      exact h

private theorem dhjThreshold_all (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    dhjThreshold k δ := by
  have h := dhjThreshold_add_two (k - 2) δ hδ
  convert h using 1
  omega

/-- **Density Hales–Jewett theorem.** Write $[k] = \{0, 1, \dots, k - 1\}$. A combinatorial line in
$[k]^N$ is given by a nonempty set of free coordinates and a fixed value in $[k]$ at every other
coordinate; its $k$ points are obtained by giving all free coordinates a common value $a \in [k]$.
For every natural number $k \ge 2$ and every real $\delta > 0$ there is a natural number $N$ such
that every set $A \subseteq [k]^N$ with $\delta k^N \le |A|$ contains all $k$ points of some
combinatorial line in $[k]^N$.

Proves `Wanted` entry `density_hales_jewett`.

Proof: We follow the density-increment route of Dodos–Kanellopoulos–Tyros, with the binary
case supplied by Sperner's theorem and the Graham–Rothschild theorem for lines.

Source: H. Furstenberg and Y. Katznelson, J. Anal. Math. 57 (1991)
and Hales-Jewett, Trans. AMS 106 (1963); Lean states finitary density form over `Fin N → Fin k`
with coloring version as corollary.
-/
public theorem density_hales_jewett :
    ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ A : Finset (Fin N → Fin k),
        δ * ((k : ℝ) ^ N) ≤ (A.card : ℝ) →
          ∃ l : Combinatorics.Line (Fin k) (Fin N), ∀ a : Fin k, l a ∈ A := by
  intro k hk δ hδ
  obtain ⟨N, hN⟩ := dhjThreshold_all k hk δ hδ
  refine ⟨N, ?_⟩
  intro A hA
  have hden : δ ≤ dhjDensity A := by
    rw [dhjDensity]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [le_div_iff₀ (by positivity)]
    exact hA
  obtain ⟨l, hl⟩ := hN N le_rfl A hden
  exact ⟨l, hl⟩

end MathlibExt.Combinatorics.DensityHalesJewettWanted
