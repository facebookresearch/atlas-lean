/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-
Compatibility source port from leanprover/cslib PR944, commit
a69a43dca61ead87b6a631854de017ddaa310e08.
Original authorship and algorithm: Fabrizio Montesi, Apache 2.0.
Only imports, explicit binders, module splitting and pinned-API bridges
are adapted here. The locked CLL Proposition and Proof are reused.
-/

module

public import CSLibExt.Logics.LinearLogic.CLL.CutCompat
public import CSLibExt.Foundations.Data.Multiset.Grind

/-! # Cut-free proofs, cut admissibility, and cut elimination for classical linear logic -/

@[expose] public section

namespace Cslib.Logic.CLL

universe u v

variable {Atom : Type u} {a b : Proposition Atom} {Γ Δ Θ : Sequent Atom}

open Cslib.Logic.InferenceSystem

/-- A proof is cut-free if it does not contain any applications of rule cut. -/
@[simp]
def Proof.IsCutFree {Γ : Sequent Atom} : ⇓Γ → Prop
  | ax | one | top => True
  | bot p | parr p | oplus₁ p | oplus₂ p
    | quest p | weaken p | contract p | bang _ p => p.IsCutFree
  | tensor p q | .with p q => p.IsCutFree ∧ q.IsCutFree
  | cut _ _ => False

/-- The source predicate agrees exactly with the pinned Boolean predicate. -/
theorem Proof.isCutFree_iff_cutFree {Γ : Sequent Atom} (p : Proof Γ) :
    p.IsCutFree ↔ p.cutFree := by
  induction p <;> simp_all [Proof.IsCutFree, Proof.cutFree]

theorem isCutFree_ax {a : Proposition Atom} :
    @Proof.IsCutFree Atom {a, a⫠} (Proof.ax (a := a)) := ⟨⟩

theorem isCutFree_one : @Proof.IsCutFree Atom {1} Proof.one := ⟨⟩

theorem isCutFree_top {Γ : Sequent Atom} :
    @Proof.IsCutFree Atom (⊤ ::ₘ Γ) (Proof.top (Γ := Γ)) := ⟨⟩

theorem isCutFree_bot {Γ : Sequent Atom} {p : Proof Γ} (hp : @Proof.IsCutFree Atom Γ p) :
    @Proof.IsCutFree Atom (⊥ ::ₘ Γ) (Proof.bot (Γ := Γ) p) := hp

theorem isCutFree_parr {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ b ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⅋ b) ::ₘ Γ) (Proof.parr (a := a) (b := b) (Γ := Γ) p) := hp

theorem isCutFree_tensor {a b : Proposition Atom} {Γ Δ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} {q : Proof (b ::ₘ Δ)}
    (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p)
    (hq : @Proof.IsCutFree Atom (b ::ₘ Δ) q) :
    @Proof.IsCutFree Atom ((a ⊗ b) ::ₘ (Γ + Δ))
      (Proof.tensor (a := a) (b := b) (Γ := Γ) (Δ := Δ) p q) :=
  And.intro hp hq

theorem isCutFree_oplus₁ {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⊕ b) ::ₘ Γ) (Proof.oplus₁ (a := a) (b := b) (Γ := Γ) p) := hp

theorem isCutFree_oplus₂ {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (b ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⊕ b) ::ₘ Γ) (Proof.oplus₂ (a := a) (b := b) (Γ := Γ) p) := hp

theorem isCutFree_with {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} {q : Proof (b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p)
    (hq : @Proof.IsCutFree Atom (b ::ₘ Γ) q) :
    @Proof.IsCutFree Atom ((a & b) ::ₘ Γ) (Proof.with (a := a) (b := b) (Γ := Γ) p q) :=
  And.intro hp hq

theorem isCutFree_quest {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.quest (a := a) (Γ := Γ) p) := hp

theorem isCutFree_weaken {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof Γ} (hp : @Proof.IsCutFree Atom Γ p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.weaken (a := a) (Γ := Γ) p) := hp

theorem isCutFree_contract {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (ʔa ::ₘ ʔa ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (ʔa ::ₘ ʔa ::ₘ Γ) p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.contract (a := a) (Γ := Γ) p) := hp

theorem isCutFree_bang {a : Proposition Atom} {Γ : Sequent Atom}
    {hΓ : Γ.allQuest} {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((!a) ::ₘ Γ) (Proof.bang (a := a) (Γ := Γ) hΓ p) := hp

/-- Recursor for cut-free proofs: never sees the `cut` case. -/
@[induction_eliminator, cases_eliminator, elab_as_elim]
def Proof.IsCutFree.rec
    {motive : {Γ : Sequent Atom} → {p : Proof Γ} → (h : p.IsCutFree) → Sort v}
    (ax : ∀ {a : Proposition Atom}, @motive {a, a⫠} .ax (isCutFree_ax (a := a)))
    (one : @motive {1} .one isCutFree_one)
    (top : ∀ {Γ}, @motive (⊤ ::ₘ Γ) .top (isCutFree_top (Γ := Γ)))
    (bot : ∀ {Γ} (p : Proof Γ) {hp}, @motive Γ p hp →
      @motive (⊥ ::ₘ Γ) (.bot p) (isCutFree_bot hp))
    (parr : ∀ {a b Γ} (p : Proof (a ::ₘ b ::ₘ Γ)) {hp},
      @motive (a ::ₘ b ::ₘ Γ) p hp →
      @motive ((a ⅋ b) ::ₘ Γ) (.parr p) (isCutFree_parr hp))
    (tensor : ∀ {a b Γ Δ} (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Δ)) {hp hq},
      @motive (a ::ₘ Γ) p hp → @motive (b ::ₘ Δ) q hq →
      @motive ((a ⊗ b) ::ₘ (Γ + Δ)) (.tensor p q) (isCutFree_tensor hp hq))
    (oplus₁ : ∀ {a b Γ} (p : Proof (a ::ₘ Γ)) {hp},
      @motive (a ::ₘ Γ) p hp →
      @motive ((a ⊕ b) ::ₘ Γ) (.oplus₁ p) (isCutFree_oplus₁ hp))
    (oplus₂ : ∀ {a b Γ} (p : Proof (b ::ₘ Γ)) {hp},
      @motive (b ::ₘ Γ) p hp →
      @motive ((a ⊕ b) ::ₘ Γ) (.oplus₂ p) (isCutFree_oplus₂ hp))
    («with» : ∀ {a b Γ} (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Γ)) {hp hq},
      @motive (a ::ₘ Γ) p hp → @motive (b ::ₘ Γ) q hq →
      @motive ((a & b) ::ₘ Γ) (.with p q) (isCutFree_with hp hq))
    (quest : ∀ {a Γ} (p : Proof (a ::ₘ Γ)) {hp},
      @motive (a ::ₘ Γ) p hp →
      @motive (ʔa ::ₘ Γ) (.quest p) (isCutFree_quest hp))
    (weaken : ∀ {a Γ} (p : Proof Γ) {hp},
      @motive Γ p hp →
      @motive (ʔa ::ₘ Γ) (.weaken p) (isCutFree_weaken hp))
    (contract : ∀ {a Γ} (p : Proof (ʔa ::ₘ ʔa ::ₘ Γ)) {hp},
      @motive (ʔa ::ₘ ʔa ::ₘ Γ) p hp →
      @motive (ʔa ::ₘ Γ) (.contract p) (isCutFree_contract hp))
    (bang : ∀ {a} {Γ : Sequent Atom} (hΓ : Γ.allQuest) (p : Proof (a ::ₘ Γ)) {hp},
      @motive (a ::ₘ Γ) p hp →
      @motive ((!a) ::ₘ Γ) (.bang hΓ p) (isCutFree_bang hp))
    {Γ} {p} (h : p.IsCutFree) : @motive Γ p h :=
  let rec go {Γ : Sequent Atom} {p : Proof Γ} (h : p.IsCutFree) : @motive Γ p h :=
    match p, h with
    | .ax, _ => ax
    | .one, _ => one
    | .top, _ => top
    | .bot p, hp => bot p (go (p := p) hp)
    | .parr p, hp => parr p (go (p := p) hp)
    | .tensor p q, hpq => tensor p q (go hpq.1) (go hpq.2)
    | .oplus₁ p, hp => oplus₁ p (go (p := p) hp)
    | .oplus₂ p, hp => oplus₂ p (go (p := p) hp)
    | .with p q, hpq => «with» p q (go hpq.1) (go hpq.2)
    | .quest p, hp => quest p (go (p := p) hp)
    | .weaken p, hp => weaken p (go (p := p) hp)
    | .contract p, hp => contract p (go (p := p) hp)
    | .bang hΓ p, hp => bang hΓ p (go (p := p) hp)
    | .cut _ _, h => nomatch h
  go h

/-- Transporting a conclusion preserves cut-freeness. -/
@[simp, scoped grind .]
theorem Proof.isCutFree_rwConclusion (h : Γ = Δ) (p : Proof Γ)
    (hp : p.IsCutFree) : (p.rwConclusion h).IsCutFree := by grind

/-- Tag for the cut-free fragment of CLL. -/
opaque CF : Type := Empty

namespace CF

open scoped CLL.Proof Sequent

/-- Proofs in the CF inference system. -/
abbrev Proof (Γ : Sequent Atom) := { p : ⇓Γ // p.IsCutFree }

instance : InferenceSystem CF (Sequent Atom) := ⟨CF.Proof⟩

instance {Γ : Sequent Atom} : Coe (CF⇓Γ) (⇓Γ) where
  coe p := p.val

/-- Rewrites the conclusion of a cut-free proof.
If `h` is omitted, tries to prove the equality using `grind only [multiset]`. -/
def Proof.rwConclusion {Γ Δ : Sequent Atom} (h : Γ = Δ := by grind only [multiset]) (p : CF⇓Γ) :
    CF⇓Δ := ⟨CLL.Proof.rwConclusion h p.val, CLL.Proof.isCutFree_rwConclusion h p.val p.property⟩

@[simp, scoped grind =]
theorem Proof.rwConclusion_val {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : CF⇓Γ) :
    (p.rwConclusion h).val = CLL.Proof.rwConclusion h p.val := rfl

/-- Axiom for CF. -/
def Proof.ax {a : Proposition Atom} : CF⇓({a, a⫠} : Sequent Atom) := ⟨CLL.Proof.ax, isCutFree_ax⟩

/-- Rule `1` for CF. -/
def Proof.one : CF⇓({1} : Sequent Atom) := ⟨CLL.Proof.one, isCutFree_one⟩

/-- Rule `⊤` for CF. -/
def Proof.top {Γ : Sequent Atom} :
    CF⇓((⊤ : Proposition Atom) ::ₘ Γ) :=
  ⟨CLL.Proof.top, isCutFree_top⟩

/-- Rule `⊥` for CF. -/
def Proof.bot {Γ : Sequent Atom} (p : CF⇓Γ) : CF⇓(⊥ ::ₘ Γ) :=
  ⟨CLL.Proof.bot p.val, isCutFree_bot p.property⟩

/-- Rule `⅋` for CF. -/
def Proof.parr {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ b ::ₘ Γ)) :
    CF⇓((a ⅋ b) ::ₘ Γ) := ⟨CLL.Proof.parr p.val, isCutFree_parr p.property⟩

/-- Rule `⊗` for CF. -/
def Proof.tensor {a b : Proposition Atom} {Γ Δ : Sequent Atom}
    (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(b ::ₘ Δ)) : CF⇓((a ⊗ b) ::ₘ (Γ + Δ)) :=
  ⟨CLL.Proof.tensor p.val q.val, isCutFree_tensor p.property q.property⟩

/-- Rule `⊕₁` for CF. -/
def Proof.oplus₁ {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) :
    CF⇓((a ⊕ b) ::ₘ Γ) :=
  ⟨CLL.Proof.oplus₁ p.val, isCutFree_oplus₁ p.property⟩

/-- Rule `⊕₂` for CF. -/
def Proof.oplus₂ {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(b ::ₘ Γ)) :
    CF⇓((a ⊕ b) ::ₘ Γ) :=
  ⟨CLL.Proof.oplus₂ p.val, isCutFree_oplus₂ p.property⟩

/-- Rule `&` for CF. -/
def Proof.with {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(b ::ₘ Γ)) :
    CF⇓((a & b) ::ₘ Γ) := ⟨CLL.Proof.with p.val q.val, isCutFree_with p.property q.property⟩

/-- Rule `?` (dereliction) for CF. -/
def Proof.quest {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) : CF⇓(ʔa ::ₘ Γ) :=
  ⟨CLL.Proof.quest p.val, isCutFree_quest p.property⟩

/-- Rule `?` (weaken) for CF. -/
def Proof.weaken {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓Γ) : CF⇓(ʔa ::ₘ Γ) :=
  ⟨CLL.Proof.weaken p.val, isCutFree_weaken p.property⟩

/-- Rule `?` (contract) for CF. -/
def Proof.contract {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(ʔa ::ₘ ʔa ::ₘ Γ)) :
    CF⇓(ʔa ::ₘ Γ) := ⟨CLL.Proof.contract p.val, isCutFree_contract p.property⟩

/-- Rule `!` (bang/promotion) for CF. -/
def Proof.bang {a : Proposition Atom} {Γ : Sequent Atom} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) :
    CF⇓((!a) ::ₘ Γ) := ⟨CLL.Proof.bang hΓ p.val, isCutFree_bang p.property⟩

/-- Given a list of `ʔ`-propositions `Γ`, transforms a cut-free proof of `Δ` into a proof of `Γ + Δ`
via weakening. -/
def Proof.weakenContext {Γ : List (Proposition Atom)} {Δ : Sequent Atom} (hΓ : Γ.allQuest)
    (p : CF⇓Δ) : CF⇓(Γ + Δ) :=
  match Γ, hΓ with
  | [], _ => p.rwConclusion (Multiset.zero_add Δ).symm
  | .quest a :: Γ, hΓ =>
    (Proof.weaken (a := a) (Proof.weakenContext (Γ := Γ) hΓ p)).rwConclusion
  | .atom _ :: _, hΓ | .atomDual _ :: _, hΓ
    | .one :: _, hΓ | .zero :: _, hΓ | .top :: _, hΓ | .bot :: _, hΓ
    | .tensor _ _ :: _, hΓ | .parr _ _ :: _, hΓ
    | .oplus _ _ :: _, hΓ | .with _ _ :: _, hΓ | .bang _ :: _, hΓ =>
    nomatch hΓ

/-- Given a list of `ʔ`-propositions `Γ`, transforms a proof of `Γ + Γ + Δ` into a proof of `Γ + Δ`
via contraction. -/
def Proof.contractContext {Γ : List (Proposition Atom)} {Δ : Sequent Atom} (hΓ : Γ.allQuest)
    (p : CF⇓((Γ : Sequent Atom) + Γ + Δ)) : CF⇓(Γ + Δ) :=
  match Γ, hΓ with
  | [], _ => p.rwConclusion
  | .quest a :: Γ, hΓ =>
    let p' : CF⇓(ʔa ::ₘ ʔa ::ₘ ((Γ : Sequent Atom) + Γ + Δ)) := p.rwConclusion
    let p' : CF⇓(ʔa ::ₘ ((Γ : Sequent Atom) + Γ + Δ)) := Proof.contract p'
    let p' : CF⇓((Γ : Sequent Atom) + Γ + (ʔa ::ₘ Δ)) := p'.rwConclusion
    (Proof.contractContext (Γ := Γ) (Δ := ʔa ::ₘ Δ) hΓ p').rwConclusion
  | .atom _ :: _, hΓ | .atomDual _ :: _, hΓ
    | .one :: _, hΓ | .zero :: _, hΓ | .top :: _, hΓ | .bot :: _, hΓ
    | .tensor _ _ :: _, hΓ | .parr _ _ :: _, hΓ
    | .oplus _ _ :: _, hΓ | .with _ _ :: _, hΓ | .bang _ :: _, hΓ =>
    nomatch hΓ

end CF

open scoped CF.Proof

namespace Sequent

-- The pin derives BEq independently of DecidableEq. The source derives
-- only DecidableEq, so list erasure must use the corresponding lawful BEq.
local instance [DecidableEq Atom] : BEq (Proposition Atom) := instBEqOfDecidableEq

/-- An empty sum has an empty right residual context. -/
theorem eq_zero_of_zero_eq_add (h : (0 : Sequent Atom) = Γ + Δ) : Δ = 0 := by
  apply Multiset.le_zero.mp
  rw [h]
  exact Multiset.le_add_left _ _

/-- Distinguish a principal selected occurrence using decidable equality.
Given `a ::ₘ Γ = b ::ₘ Δ`, either `a = b` and `Γ = Δ`, or `a ≠ b` and the propositions are swapped:
`Γ = b ::ₘ Λ` and `Δ = a ::ₘ Λ` for some `Λ`.
The tail `Δ` can be an arbitrary multiset; the residual list is obtained from `Γ`. -/
def splitCons [DecidableEq Atom] {Γ : List (Proposition Atom)} {Δ : Sequent Atom}
    (h : a ::ₘ Γ = b ::ₘ Δ) :
    (a = b ∧ (Γ : Sequent Atom) = Δ) ⊕'
      {Θ : List (Proposition Atom) //
        a ≠ b ∧ (Γ : Sequent Atom) = b ::ₘ Θ ∧ Δ = a ::ₘ Θ} := by
  by_cases hab : a = b
  · subst b
    exact .inl ⟨rfl, (Multiset.cons_inj_right a).mp h⟩
  · have hba : b ≠ a := Ne.symm hab
    have hbΓ : b ∈ (Γ : Sequent Atom) := by
      have hb : b ∈ a ::ₘ (Γ : Sequent Atom) := by
        rw [h]
        simp
      simpa [hba] using hb
    have hΓ : (Γ : Sequent Atom) = b ::ₘ (Γ.erase b : Sequent Atom) := by
      exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase hbΓ)
    have hΔ : Δ = a ::ₘ (Γ.erase b : Sequent Atom) := by
      grind only [multiset]
    exact .inr ⟨Γ.erase b, hab, hΓ, hΔ⟩

/-- Given `a ::ₘ Γ = (Δ : Sequent) + Θ`, locate `a` in either `Δ` or `Θ` and
erase it from that summand, returning the residual list. -/
def splitConsAdd [DecidableEq Atom] {Γ Δ Θ : List (Proposition Atom)}
    (h : a ::ₘ Γ = (Δ : Sequent Atom) + Θ) :
    {Δ' : List (Proposition Atom) //
      (Δ : Sequent Atom) = a ::ₘ Δ' ∧ (Γ : Sequent Atom) = (Δ' : Sequent Atom) + Θ} ⊕'
    {Θ' : List (Proposition Atom) //
      (Θ : Sequent Atom) = a ::ₘ Θ' ∧ (Γ : Sequent Atom) = (Δ : Sequent Atom) + Θ'} := by
  by_cases haΔ : a ∈ (Δ : Sequent Atom)
  · have hΔ : (Δ : Sequent Atom) = a ::ₘ (Δ.erase a : Sequent Atom) := by
      exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase haΔ)
    have hΓ : (Γ : Sequent Atom) = (Δ.erase a : Sequent Atom) + Θ := by grind only [multiset]
    exact .inl ⟨Δ.erase a, hΔ, hΓ⟩
  · have haΘ : a ∈ (Θ : Sequent Atom) := by
      have ha : a ∈ (Δ : Sequent Atom) + Θ := by grind only [multiset]
      grind only [multiset]
    have hΘ : (Θ : Sequent Atom) = a ::ₘ (Θ.erase a : Sequent Atom) := by
      exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase haΘ)
    have hΓ : (Γ : Sequent Atom) = (Δ : Sequent Atom) + (Θ.erase a : Sequent Atom) := by
      grind only [multiset]
    exact .inr ⟨Θ.erase a, hΘ, hΓ⟩

/-- Given `Multiset.replicate n a + Γ = b ::ₘ Δ`, either the head `b` is one of the
`n` copies of `a` (so `b = a` and the tail is `replicate (n-1) a + Γ`), or `b` belongs to
`Γ` (so `Δ = Multiset.replicate n a + Γ'` where `Γ = b ::ₘ Γ'`).
The tail `Δ` can be an arbitrary multiset; the residual list is obtained from `Γ`. -/
def splitReplicateCons [DecidableEq Atom] {Γ : List (Proposition Atom)} {Δ : Sequent Atom} {n : ℕ}
    (h : Multiset.replicate n a + Γ = b ::ₘ Δ) :
    {m : ℕ // n = m + 1 ∧ b = a ∧ Δ = Multiset.replicate m a + Γ} ⊕'
      {Γ' : List (Proposition Atom) // (Γ : Sequent Atom) = b ::ₘ Γ' ∧
        Δ = Multiset.replicate n a + Γ'} := by
  by_cases hs : n ≠ 0 ∧ b = a
  · obtain ⟨hn, rfl⟩ := hs
    cases n with
    | zero => exact (hn rfl).elim
    | succ m =>
        refine .inl ⟨m, rfl, rfl, ?_⟩
        grind only [multiset]
  · have hbΓ : b ∈ (Γ : Sequent Atom) := by
      have hb : b ∈ Multiset.replicate n a + (Γ : Sequent Atom) := by
        rw [h]
        simp
      rcases Multiset.mem_add.mp hb with hb | hb
      · exact (hs (Multiset.mem_replicate.mp hb)).elim
      · exact hb
    have hΓ : (Γ : Sequent Atom) = b ::ₘ (Γ.erase b : Sequent Atom) :=
      Multiset.coe_eq_coe.mpr (List.perm_cons_erase hbΓ)
    have ht : Δ = Multiset.replicate n a + (Γ.erase b : Sequent Atom) := by
      grind only [multiset]
    exact .inr ⟨Γ.erase b, hΓ, ht⟩

/-- Given `Multiset.replicate n a + Γ = (Δ : Sequent) + Θ`, split the `n` copies of `a`
between `Δ` and `Θ`, returning counts `k` and `l` and residual lists. -/
def splitReplicateAdd [DecidableEq Atom] {Γ Δ Θ : List (Proposition Atom)} {n : ℕ}
    (h : Multiset.replicate n a + Γ = (Δ : Sequent Atom) + Θ) :
    Σ (k l : ℕ) (Δ' : List (Proposition Atom)),
      {Θ' : List (Proposition Atom) // n = k + l ∧
        (Δ : Sequent Atom) = Multiset.replicate k a + Δ' ∧
        (Θ : Sequent Atom) = Multiset.replicate l a + Θ' ∧
        (Γ : Sequent Atom) = (Δ' : Sequent Atom) + Θ'} := by
  induction n generalizing Δ Θ with
  | zero =>
      refine ⟨0, 0, Δ, ⟨Θ, ?_⟩⟩
      simpa using h
  | succ n ih =>
      have hR : ((List.replicate n a ++ Γ : List (Proposition Atom)) : Sequent Atom) =
          Multiset.replicate n a + (Γ : Sequent Atom) := by
        grind only [multiset]
      have hHead : a ::ₘ ((List.replicate n a ++ Γ : List (Proposition Atom)) : Sequent Atom) =
          (Δ : Sequent Atom) + Θ := by
        rw [hR]
        simpa [Nat.succ_eq_add_one, Multiset.replicate_succ] using h
      cases splitConsAdd (a := a) (Γ := List.replicate n a ++ Γ) (Δ := Δ) (Θ := Θ) hHead with
      | inl r =>
          rcases r with ⟨Δ₁, hΔ, hrest⟩
          rw [hR] at hrest
          rcases ih (Δ := Δ₁) (Θ := Θ) hrest with ⟨k, l, Δ', Θ', hn, hΔ₁, hΘ, hΓ⟩
          refine ⟨Nat.succ k, l, Δ', ⟨Θ', ?_, ?_, hΘ, hΓ⟩⟩ <;> grind only [multiset]
      | inr r =>
          rcases r with ⟨Θ₁, hΘ, hrest⟩
          rw [hR] at hrest
          rcases ih (Δ := Δ) (Θ := Θ₁) hrest with ⟨k, l, Δ', Θ', hn, hΔ, hΘ₁, hΓ⟩
          refine ⟨k, Nat.succ l, Δ', ⟨Θ', ?_, hΔ, ?_, hΓ⟩⟩ <;> grind only [multiset]

end Sequent

end Cslib.Logic.CLL
