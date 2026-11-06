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

public import CSLibExt.Logics.LinearLogic.CLL.CutFree

/-! # Source exponential multicut for the locked CLL calculus -/

@[expose] public section

namespace Cslib.Logic.CLL

open Cslib.Logic.InferenceSystem
open scoped CF.Proof

universe u

variable {Atom : Type u} {a b : Proposition Atom} {Γ Δ Θ : Sequent Atom}

/-- **Cut admissibility at a fixed proposition.**
Cut admissibility at a fixed proposition `a`: for any list sequents `Γ`, `Δ`, given
cut-free proofs of `a ::ₘ Γ` and `a⫠ ::ₘ Δ`, produce a cut-free proof of
`(Γ : Sequent Atom) + Δ`. -/
abbrev CutAdmissibleAt (a : Proposition Atom) := ∀ {Γ Δ : List (Proposition Atom)},
  CF⇓(a ::ₘ Γ) → CF⇓(a⫠ ::ₘ Δ) → CF⇓((Γ : Sequent Atom) + Δ)

/-- **Cut admissibility below a size bound.**
The outer induction hypothesis for cut admissibility: for all propositions `a` with
`sizeOf a < bound`, cut is admissible at `a`. -/
abbrev CutAdmissibleBelow (Atom : Type u) (bound : ℕ) :=
  ∀ {a : Proposition Atom}, sizeOf a < bound → CutAdmissibleAt a

/-- **Locating a selected question mark or a residual head.**
Locate a selected question mark or a residual head using `Sequent.splitReplicateCons`. -/
def splitHead [DecidableEq Atom] {a b : Proposition Atom} {Θ : Sequent Atom} {n : ℕ}
    {Δ : List (Proposition Atom)}
    (h : b ::ₘ Θ = Multiset.replicate n (ʔ(a⫠)) + Δ) :
    {m : ℕ //
      n = m + 1 ∧
      b = ʔ(a⫠) ∧
      Θ = Multiset.replicate m (ʔ(a⫠)) + Δ} ⊕'
    {Δ' : List (Proposition Atom) //
      (Δ : Sequent Atom) = b ::ₘ Δ' ∧
      Θ = Multiset.replicate n (ʔ(a⫠)) + Δ'} :=
  Sequent.splitReplicateCons h.symm

/-- **Splitting replicated question marks across two summands.**
Split replicated question marks across two arbitrary multiset summands. -/
def splitAdd [DecidableEq Atom] {a : Proposition Atom} {Θ₁ Θ₂ : Sequent Atom} {n : ℕ}
    {Δ : List (Proposition Atom)}
    (h : Θ₁ + Θ₂ = Multiset.replicate n (ʔ(a⫠)) + Δ) :
    Σ k : ℕ, Σ l : ℕ, Σ Δ₁ : List (Proposition Atom),
      {Δ₂ : List (Proposition Atom) //
        n = k + l ∧
        Θ₁ = Multiset.replicate k (ʔ(a⫠)) + Δ₁ ∧
        Θ₂ = Multiset.replicate l (ʔ(a⫠)) + Δ₂ ∧
        (Δ : Sequent Atom) =
          (Δ₁ : Sequent Atom) + Δ₂} := by
  let Λ := List.replicate n (ʔ(a⫠)) ++ Δ
  have hL : (Λ : Sequent Atom) = Multiset.replicate n (ʔ(a⫠)) + Δ := by
    grind only [multiset]
  have h₁le : Θ₁ ≤ (Λ : Sequent Atom) := by
    rw [hL, ← h]
    exact Multiset.le_add_right _ _
  have h₂le : Θ₂ ≤ (Λ : Sequent Atom) := by
    rw [hL, ← h]
    exact Multiset.le_add_left _ _
  let s₁ := Multiset.scanToList Λ Θ₁ h₁le
  let s₂ := Multiset.scanToList Λ Θ₂ h₂le
  have hs₁ : (s₁.1 : Sequent Atom) = Θ₁ := s₁.2
  have hs₂ : (s₂.1 : Sequent Atom) = Θ₂ := s₂.2
  have hs : Multiset.replicate n (ʔ(a⫠)) + Δ = (s₁.1 : Sequent Atom) + s₂.1 := by
    rw [hs₁, hs₂]; exact h.symm
  rcases Sequent.splitReplicateAdd (a := ʔ(a⫠)) hs with ⟨k, l, Δ₁, Δ₂, hn, h₁, h₂, hΔ⟩
  exact ⟨k, l, Δ₁, ⟨Δ₂, hn, hs₁.symm.trans h₁, hs₂.symm.trans h₂, hΔ⟩⟩

/-- **Axiom case of the exponential multicut.**
Ax case for `questMulticut`: the selected dual question mark is one of the copies of `a⫠`.
This isolates the recursive branch from the plain-term outer proof. -/
def Proof.questMulticutAx [DecidableEq Atom] {a : Proposition Atom}
    {Γ : List (Proposition Atom)} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ))
    {c : Proposition Atom} {n : ℕ} {Δ : List (Proposition Atom)}
    (h : c ::ₘ ([c⫠] : List (Proposition Atom)) = Multiset.replicate n (ʔ(a⫠)) + Δ) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  have hs : Multiset.replicate n (ʔ(a⫠)) + Δ = c ::ₘ ([c⫠] : List (Proposition Atom)) := by
    simpa using h.symm
  rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs with hs | hs
  · rcases hs with ⟨m, hn, hc, htail⟩
    have hs₂ : Multiset.replicate m (ʔ(a⫠)) + Δ = c⫠ ::ₘ ([] : List (Proposition Atom)) := by
      simpa using htail.symm
    rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs₂ with hs₂ | hs₂
    · rcases hs₂ with ⟨_, _, hcdual, _⟩
      have : c = c⫠ := hc.trans hcdual.symm
      exact (Proposition.dual_neq c this).elim
    · rcases hs₂ with ⟨Δ', hΔ, hzero⟩
      have hΔ'zero : (Δ' : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
      have hcdual : c⫠ = !a := by
        rw [hc]
        simp [Proposition.dual]
      have hΔbang : (Δ : Sequent Atom) = ({!a} : Sequent Atom) := by
        rw [hΔ, hΔ'zero, hcdual]; rfl
      let r : CF⇓((!a) ::ₘ (Γ : Sequent Atom)) := CF.Proof.bang (by simpa using hΓ) p
      exact r.rwConclusion (by
        rw [hΔbang, Multiset.add_comm]
        exact (Multiset.singleton_add _ _).symm)
  · rcases hs with ⟨Δ₁, hΔ, htail⟩
    have hs₂ : Multiset.replicate n (ʔ(a⫠)) + Δ₁ = c⫠ ::ₘ ([] : List (Proposition Atom)) := by
      simpa using htail.symm
    rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs₂ with hs₂ | hs₂
    · rcases hs₂ with ⟨m, hn, hcdual, hzero⟩
      have hΔ₁zero : (Δ₁ : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
      have hc : c = !a := by
        have := congrArg Proposition.dual hcdual
        simpa [Proposition.dual] using this
      have hΔbang : (Δ : Sequent Atom) = ({!a} : Sequent Atom) := by
        rw [hΔ, hΔ₁zero, hc]; rfl
      let r : CF⇓((!a) ::ₘ (Γ : Sequent Atom)) := CF.Proof.bang (by simpa using hΓ) p
      exact r.rwConclusion (by
        rw [hΔbang, Multiset.add_comm]
        exact (Multiset.singleton_add _ _).symm)
    · rcases hs₂ with ⟨Δ₂, hΔ₁, hzero⟩
      have hΔ₂zero : (Δ₂ : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
      have hΔpair : (Δ : Sequent Atom) = ({c, c⫠} : Sequent Atom) := by
        rw [hΔ, hΔ₁, hΔ₂zero]; rfl
      let r : CF⇓((Γ : Sequent Atom) + ({c, c⫠} : Sequent Atom)) :=
        CF.Proof.weakenContext (by simpa using hΓ) (CF.Proof.ax (a := c))
      exact r.rwConclusion (by rw [hΔpair])

/-- **Exponential multicut against replicated question marks.**
Exponential/multicut helper: given `p : CF⇓(a ::ₘ Γ)` (the "substitutend") and
`q : CF⇓(Multiset.replicate n (ʔ(a⫠)) + Δ)` (the "supply" with `n` selected dual question marks),
produce `CF⇓((Γ : Sequent) + Δ)`. -/
def Proof.questMulticut [DecidableEq Atom] (cutSmaller : CutAdmissibleBelow Atom (sizeOf (!a)))
    {Γ Δ : List (Proposition Atom)} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) {n : ℕ}
    (q : CF⇓(Multiset.replicate n (ʔ(a⫠)) + Δ)) : CF⇓((Γ : Sequent Atom) + Δ) :=
  let hΓm : Sequent.allQuest (Γ : Sequent Atom) := by simpa using hΓ
  let haSmall : sizeOf a < sizeOf (!a) := by simp
  let motive : {Θ : Sequent Atom} → {r : Proof Θ} → (hr : r.IsCutFree) → Type u :=
    fun {Θ} {_} _ =>
      ∀ {n : ℕ} {Δ : List (Proposition Atom)},
        Θ = Multiset.replicate n (ʔ(a⫠)) + Δ →
        CF⇓((Γ : Sequent Atom) + Δ)
  (Proof.IsCutFree.rec
      (motive := motive)
      /- ax -/
      (ax := Proof.questMulticutAx hΓ p)
      /- one -/
      (one := by
        intro n Δ h
        have hs :
            Multiset.replicate n (ʔ(a⫠)) + Δ =
              (1 : Proposition Atom) ::ₘ ([] : List (Proposition Atom)) := h.symm
        rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, hzero⟩
          have hΔ'zero : (Δ' : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
          have hΔone : (Δ : Sequent Atom) = ({1} : Sequent Atom) := by
            rw [hΔ, hΔ'zero]; rfl
          let r : CF⇓((Γ : Sequent Atom) + ({1} : Sequent Atom)) :=
            CF.Proof.weakenContext hΓ
              (CF.Proof.one (Atom := Atom))
          exact r.rwConclusion (by rw [hΔone]))
      /- top -/
      (top := by
        intro Θ n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r : CF⇓((⊤ : Proposition Atom) ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            CF.Proof.top
          exact r.rwConclusion)
      /- bot -/
      (bot := by
        intro Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := Δ') htail
          exact (CF.Proof.bot r').rwConclusion)
      /- parr -/
      (parr := by
        intro c d Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: d :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ d ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          exact (CF.Proof.parr r'').rwConclusion)
      /- tensor -/
      (tensor := by
        intro c d Θ₁ Θ₂ r s hr hs ihr ihs n Δ h
        rcases splitHead h with hp | hp
        · rcases hp with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hp with ⟨Δ', hΔ, htail⟩
          rcases splitAdd htail with
            ⟨k, l, Δ₁, Δ₂, hn, h₁, h₂, hres⟩
          let r' := ihr (n := k) (Δ := c :: Δ₁) (by grind only [multiset])
          let s' := ihs (n := l) (Δ := d :: Δ₂) (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ₁)) := r'.rwConclusion
          let s'' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ₂)) := s'.rwConclusion
          let t := CF.Proof.tensor r'' s''
          let t' : CF⇓((Γ : Sequent Atom) + Γ + ((c ⊗ d) ::ₘ ((Δ₁ : Sequent Atom) + Δ₂))) :=
            t.rwConclusion
          let t'' := CF.Proof.contractContext (Γ := Γ) hΓ t'
          exact t''.rwConclusion (by rw [← hres, ← hΔ]))
      /- oplus₁ -/
      (oplus₁ := by
        intro c d Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          exact (CF.Proof.oplus₁ (b := d) r'').rwConclusion)
      /- oplus₂ -/
      (oplus₂ := by
        intro c d Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := d :: Δ') (by grind only [multiset])
          let r'' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          exact (CF.Proof.oplus₂ (a := c) r'').rwConclusion)
      /- with -/
      («with» := by
        intro c d Θ r s hr hs ihr ihs n Δ h
        rcases splitHead h with hp | hp
        · rcases hp with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hp with ⟨Δ', hΔ, htail⟩
          let r' := ihr (n := n) (Δ := c :: Δ') (by grind only [multiset])
          let s' := ihs (n := n) (Δ := d :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          let s'' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ')) := s'.rwConclusion
          exact (CF.Proof.with r'' s'').rwConclusion)
      /- quest -/
      (quest := by
        intro c Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        /- The displayed `?` is one of the selected copies. -/
        · rcases hs with ⟨m, hn, hcq, htail⟩
          have hc : c = a⫠ := by
            injection hcq
          /-
          First eliminate all the remaining selected copies, keeping the
          exposed `a⫠` as part of the residual sequent.
          -/
          let r' := ih (n := m) (Δ := c :: Δ) (by grind only [multiset])
          let r'' : CF⇓(a⫠ ::ₘ (((Γ ++ Δ : List (Proposition Atom))) : Sequent Atom)) :=
            r'.rwConclusion (by
              rw [hc]
              exact Multiset.add_cons _ (Γ : Sequent Atom) (Δ : Sequent Atom))
          /-
          Now cut the exposed `a⫠` against `p`.  This duplicates Γ.
          -/
          let t := cutSmaller haSmall p r''
          let t' : CF⇓((Γ : Sequent Atom) + Γ + Δ) := t.rwConclusion
          exact CF.Proof.contractContext (Γ := Γ) hΓ t'
        /- The displayed `?` belongs to the residual sequent. -/
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          exact (CF.Proof.quest r'').rwConclusion)
      /- weaken -/
      (weaken := by
        intro c Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        /- This weakening introduced a selected occurrence. -/
        · rcases hs with ⟨m, hn, hc, htail⟩
          exact ih (n := m) (Δ := Δ) htail
        /- It introduced an unselected occurrence. -/
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := Δ') htail
          exact (CF.Proof.weaken (a := c) r').rwConclusion)
      /- contract -/
      (contract := by
        intro c Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        /-
        A selected contracted occurrence corresponds to two selected
        occurrences in the premise.
        -/
        · rcases hs with ⟨m, hn, hc, htail⟩
          exact ih (n := n + 1) (Δ := Δ) (by grind only [multiset])
        /-
        Otherwise both copies in the premise are residual and contraction
        is rebuilt after the recursive call.
        -/
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := ʔc :: ʔc :: Δ') (by grind only [multiset])
          let r'' : CF⇓(ʔc ::ₘ ʔc ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          exact (CF.Proof.contract r'').rwConclusion)
      /- bang -/
      (bang := by
        intro c Θ hΘ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: Δ') (by grind only [multiset])
          have hΔ' : Sequent.allQuest (Δ' : Sequent Atom) := by
            have hq :
                Sequent.allQuest (Multiset.replicate n (ʔ(a⫠)) +
                  (Δ' : Sequent Atom)) := by
              rw [← htail]
              exact hΘ
            exact (Sequent.allQuest_add.mp hq).2
          have hside :
              Sequent.allQuest ((Γ : Sequent Atom) +
                (Δ' : Sequent Atom)) :=
            Sequent.allQuest_add.mpr ⟨hΓm, hΔ'⟩
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) := r'.rwConclusion
          exact (CF.Proof.bang hside r'').rwConclusion)
      q.property)
      rfl

end Cslib.Logic.CLL
