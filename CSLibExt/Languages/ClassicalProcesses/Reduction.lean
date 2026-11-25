/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.ClassicalProcesses.Typing
public import Mathlib.Logic.Relation

/-!
# Classical processes: reduction and preservation

Structural equivalence and one-step reduction for the exponential- and
quantifier-free fragment of Wadler's classical processes from
*Propositions as Sessions* (ICFP 2012), Figures 2-4 and §2.7, with the
preservation theorem (Theorem 1): a one-step reduction of a typed
process is typed in the same environment.

Two features of the source need explicit choices here. First, the source
states cut associativity and the tensor commuting conversions on typing
derivations, with a side condition on which component owns a cut
channel. `Cong` and `Step` are untyped relations on `Proc`, so
`Cong.assoc`, `commTensorLeft` and `commTensorRight` state ownership on
the process: the channel is free in the component that receives it, or
that component absorbs (`Proc.absorbs`: it reaches `⊤` along every
additive (`choice`) branch and through some component of every `cut`
and `output`, so it can hold a channel it does not use). Free names
alone would exclude typed instances where a `⊤` subprocess owns the
channel, and no condition at all lets `⊤` move a channel across the
wrong cut, which falsifies Theorem 1 (the `CongBare` counterexample in
the tests). The condition matches derivation-level ownership up to
re-derivation: on a typed process it holds exactly when some typing
derivation assigns the channel to that component
(`HasType.insert_iff_absorbs`), so every derivation-shaped instance is
included (`Cong.assoc_of_hasType`, `Step.commTensor_of_hasType`); where
either component could own the channel, both commutations are admitted
although a fixed derivation picks one. Figure 4's printed `fn`
conditions on `κ⊗` are the free-name half of the condition.
Second, the axiom-cut step is included in both link orientations; the
symmetric orientation is an extension of Figure 2, recorded as
`axCutSymm`. Two misprints in §2.7 are corrected: the closure rule's
conclusion is a reduction, and the second reduction-under-cut rule
reduces the right component. One-step reduction includes the principal,
commuting-conversion and cut-congruence rules of Figures 2-4, closed
under structural equivalence; `Steps` is its reflexive-transitive
closure.

Deadlock freedom (Theorem 2) is not formalized here. The finite-map
context algebra supporting these proofs is developed alongside.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.ClassicalProcesses

variable {Atom : Type u}

/-! ## Channel-name and context algebra -/

/-- Lifting a channel name is injective at every cutoff. -/
theorem liftName_injective (c : ℕ) :
    Function.Injective (PiCalculus.liftName c) := by
  intro a b h
  rcases a with n | i <;> rcases b with m | j <;> simp only [PiCalculus.liftName] at h
  · exact h
  all_goals split_ifs at h <;> simp only [PiCalculus.Name.var.injEq] at h ⊢ <;> omega

/-- Exchanging the two innermost de Bruijn variables is injective. -/
theorem swapNameAt_injective : Function.Injective (PiCalculus.swapNameAt 0) := by
  intro a b h
  rcases a with n | i <;> rcases b with m | j <;> simp only [PiCalculus.swapNameAt] at h
  · exact h
  all_goals split_ifs at h <;>
    simp only [reduceCtorEq, PiCalculus.Name.var.injEq] at h ⊢ <;> omega

/-- Exchanging the two innermost de Bruijn variables is involutive. -/
theorem swapNameAt_involutive :
    Function.Involutive (PiCalculus.swapNameAt 0) := by
  intro x
  rcases x with n | _ | _ | i
  · rfl
  · rfl
  · rfl
  · simp only [PiCalculus.swapNameAt, show i + 2 ≠ 0 by omega, show i + 2 ≠ 0 + 1 by omega,
      ↓reduceIte]

/-- Lifting a renaming under a binder commutes with lifting a name. -/
theorem liftRename_liftName (g : PiCalculus.Name → PiCalculus.Name)
    (x : PiCalculus.Name) :
    liftRename g (PiCalculus.liftName 0 x) = PiCalculus.liftName 0 (g x) := by
  cases x with
  | const n => rfl
  | var i => rfl

/-- Renaming a process by a name lift is the syntactic process lift. -/
theorem Proc.rename_liftName (c : ℕ) (p : Proc Atom) :
    p.rename (PiCalculus.liftName c) = p.liftAt c := by
  have hl : ∀ c : ℕ, liftRename (PiCalculus.liftName c) = PiCalculus.liftName (c + 1) := by
    intro c
    funext x
    rcases x with n | _ | i
    · rfl
    · rfl
    · simp only [liftRename]
      by_cases hci : c ≤ i
      · simp only [PiCalculus.liftName, hci, ↓reduceIte, Nat.zero_le,
          show c + 1 ≤ i + 1 by omega]
      · simp only [PiCalculus.liftName, hci, ↓reduceIte, Nat.zero_le,
          show ¬ c + 1 ≤ i + 1 by omega]
  induction p generalizing c with
  | link x y => rfl
  | cut a p q ihp ihq => simp only [Proc.rename, Proc.liftAt, hl, ihp, ihq]
  | output x p q ihp ihq => simp only [Proc.rename, Proc.liftAt, hl, ihp, ihq]
  | input x p ih => simp only [Proc.rename, Proc.liftAt, hl, ih]
  | selectLeft x p ih => simp only [Proc.rename, Proc.liftAt, ih]
  | selectRight x p ih => simp only [Proc.rename, Proc.liftAt, ih]
  | choice x p q ihp ihq => simp only [Proc.rename, Proc.liftAt, ihp, ihq]
  | emptyOutput x => rfl
  | emptyInput x p ih => simp only [Proc.rename, Proc.liftAt, ih]
  | emptyChoice x => rfl

/-- Renaming composes: renaming by `g` after `f` is renaming by `g ∘ f`. -/
theorem Proc.rename_comp (f g : PiCalculus.Name → PiCalculus.Name)
    (p : Proc Atom) :
    (p.rename f).rename g = p.rename (g ∘ f) := by
  have hc : ∀ f g : PiCalculus.Name → PiCalculus.Name,
      liftRename g ∘ liftRename f = liftRename (g ∘ f) := by
    intro f g
    funext x
    rcases x with n | _ | i
    · exact liftRename_liftName g (f (.const n))
    · rfl
    · exact liftRename_liftName g (f (.var i))
  induction p generalizing f g with
  | link x y => rfl
  | cut a p q ihp ihq => simp only [Proc.rename, ihp, ihq, hc]
  | output x p q ihp ihq => simp only [Proc.rename, ihp, ihq, hc, Function.comp_apply]
  | input x p ih => simp only [Proc.rename, ih, hc, Function.comp_apply]
  | selectLeft x p ih => simp only [Proc.rename, ih, Function.comp_apply]
  | selectRight x p ih => simp only [Proc.rename, ih, Function.comp_apply]
  | choice x p q ihp ihq => simp only [Proc.rename, ihp, ihq, Function.comp_apply]
  | emptyOutput x => rfl
  | emptyInput x p ih => simp only [Proc.rename, ih, Function.comp_apply]
  | emptyChoice x => rfl

/-- Exchanging the two innermost variables after lifting at `0` is
lifting at `1`. -/
theorem swapNameAt_comp_liftName :
    PiCalculus.swapNameAt 0 ∘ PiCalculus.liftName 0 =
      PiCalculus.liftName 1 := by
  funext x
  rcases x with n | _ | i
  · rfl
  · rfl
  · simp only [Function.comp_apply, PiCalculus.liftName, PiCalculus.swapNameAt,
      Nat.zero_le, show 1 ≤ i + 1 by omega, ↓reduceIte, show i + 1 + 1 ≠ 0 by omega,
      show i + 1 + 1 ≠ 0 + 1 by omega]

/-- Mapping context keys twice is one map by the composite renaming. -/
theorem Context.mapKeys_comp {f g : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (Γ : Context Atom) :
    (Γ.mapKeys f hf).mapKeys g hg = Γ.mapKeys (g ∘ f) (hg.comp hf) :=
  Finmap.ext (Multiset.map_map _ _ _)

/-- Lifting at cutoff `1` after lifting at `0` is lifting at `0` twice. -/
theorem liftName_one_comp_liftName_zero :
    PiCalculus.liftName 1 ∘ PiCalculus.liftName 0 =
      PiCalculus.liftName 0 ∘ PiCalculus.liftName 0 := by
  funext x
  rcases x with n | i
  · rfl
  · simp only [Function.comp_apply, PiCalculus.liftName, Nat.zero_le, ↓reduceIte,
      show 1 ≤ i + 1 by omega]

/-- Membership of a value in a lookup of a key-mapped context. -/
private theorem mem_lookup_mapKeys {f : PiCalculus.Name → PiCalculus.Name}
    {hf : Function.Injective f} {Γ : Context Atom} {y : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} :
    (Γ.mapKeys f hf).lookup y = some v ↔ ∃ x, f x = y ∧ Γ.lookup x = some v := by
  simp only [Finmap.lookup_eq_some_iff, Context.mapKeys, Multiset.mem_map]
  constructor
  · rintro ⟨⟨x, w⟩, hmem, he⟩
    simp only [Sigma.mk.injEq, heq_eq_eq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨x, rfl, hmem⟩
  · rintro ⟨x, rfl, hmem⟩
    exact ⟨⟨x, v⟩, hmem, rfl⟩

/-- Lookup of a mapped key in a key-mapped context. -/
private theorem lookup_mapKeys_apply {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) (Γ : Context Atom) (x : PiCalculus.Name) :
    (Γ.mapKeys f hf).lookup (f x) = Γ.lookup x := by
  apply Option.ext
  intro v
  rw [mem_lookup_mapKeys]
  constructor
  · rintro ⟨x', hx', hv⟩
    rw [← hf hx']
    exact hv
  · intro hv
    exact ⟨x, rfl, hv⟩

/-- Lookup outside the range of the key map is empty. -/
private theorem lookup_mapKeys_of_forall_ne {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) (Γ : Context Atom) {y : PiCalculus.Name}
    (hy : ∀ x, f x ≠ y) : (Γ.mapKeys f hf).lookup y = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨x, hx, _⟩ := mem_lookup_mapKeys.mp hv
  exact hy x hx

/-- Membership in a key-mapped context. -/
private theorem mem_mapKeys {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Γ : Context Atom} {y : PiCalculus.Name} :
    y ∈ Γ.mapKeys f hf ↔ ∃ x ∈ Γ, f x = y := by
  simp only [Finmap.mem_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx, hv'⟩ := mem_lookup_mapKeys.mp hv
    exact ⟨x, ⟨v, hv'⟩, hx⟩
  · rintro ⟨x, ⟨v, hv⟩, rfl⟩
    exact ⟨v, by rw [lookup_mapKeys_apply]; exact hv⟩

/-- Key maps by equal renamings agree. -/
private theorem mapKeys_congr {f g : PiCalculus.Name → PiCalculus.Name}
    {hf : Function.Injective f} {hg : Function.Injective g} (h : f = g)
    (Γ : Context Atom) : Γ.mapKeys f hf = Γ.mapKeys g hg := by
  subst h
  rfl

/-- A channel is in a lifted context exactly when it is the lift of a
member of the original context. -/
theorem mem_lift {Γ : Context Atom} {y : PiCalculus.Name} :
    y ∈ Γ.lift ↔ ∃ x ∈ Γ, PiCalculus.liftName 0 x = y :=
  mem_mapKeys _

/-- The innermost bound variable is never in a lifted context. -/
theorem var_zero_not_mem_lift (Γ : Context Atom) :
    PiCalculus.Name.var 0 ∉ Γ.lift := by
  intro h
  obtain ⟨x, _, hx⟩ := mem_lift.mp h
  rcases x with n | i
  · simp only [PiCalculus.liftName, reduceCtorEq] at hx
  · simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, PiCalculus.Name.var.injEq] at hx
    omega

/-- A context none of whose entries is the innermost bound variable is
the lift of a lowered context. -/
theorem exists_unlift {Γ : Context Atom} (h : PiCalculus.Name.var 0 ∉ Γ) :
    ∃ Δ : Context Atom, Δ.lift = Γ := by
  let u : PiCalculus.Name → PiCalculus.Name := fun
    | .const n => .const n
    | .var i => .var (i - 1)
  have hkeys : ∀ k ∈ Γ.entries.keys, k ≠ .var 0 := by
    intro k hk hk0
    subst hk0
    exact h (Finmap.mem_def.mpr hk)
  have hlu : ∀ k, k ≠ .var 0 → PiCalculus.liftName 0 (u k) = k := by
    intro k hk
    rcases k with n | i
    · rfl
    · have hi : i ≠ 0 := fun hi => hk (by rw [hi])
      simp only [u, PiCalculus.liftName, Nat.zero_le, ↓reduceIte, PiCalculus.Name.var.injEq]
      omega
  refine ⟨⟨Γ.entries.map (fun e => ⟨u e.1, e.2⟩), ?_⟩, ?_⟩
  · rw [← Multiset.nodup_keys]
    have hn : Γ.entries.keys.Nodup := Γ.nodupKeys.nodup_keys
    have hk : (Multiset.map (fun e : Σ _ : PiCalculus.Name, Logic.CLL.Proposition Atom =>
          (⟨u e.1, e.2⟩ : Σ _ : PiCalculus.Name, Logic.CLL.Proposition Atom)) Γ.entries).keys =
        Γ.entries.keys.map u := by
      simp only [Multiset.keys, Multiset.map_map, Function.comp_def]
    rw [hk]
    refine hn.map_on ?_
    intro a ha b hb hab
    rw [← hlu a (hkeys a ha), ← hlu b (hkeys b hb), hab]
  · apply Finmap.ext
    simp only [Context.lift, Context.mapKeys, Multiset.map_map, Function.comp_def]
    conv_rhs => rw [← Multiset.map_id Γ.entries]
    refine Multiset.map_congr rfl ?_
    intro e he
    rw [hlu e.1 (hkeys e.1 (Multiset.mem_map_of_mem _ he))]
    rfl

/-- Key mapping sends insertion to insertion of the mapped key. -/
theorem mapKeys_insert {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Γ : Context Atom}
    {k : PiCalculus.Name} {v : Logic.CLL.Proposition Atom} :
    Context.mapKeys f hf (Γ.insert k v) = (Γ.mapKeys f hf).insert (f k) v := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [lookup_mapKeys_apply]
    by_cases hxk : x = k
    · subst hxk
      rw [Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hxk,
        Finmap.lookup_insert_of_ne _ (fun h => hxk (hf h)), lookup_mapKeys_apply]
  · simp only [not_exists] at hy
    rw [lookup_mapKeys_of_forall_ne hf _ hy, Finmap.lookup_insert_of_ne _ (fun h => hy k h.symm),
      lookup_mapKeys_of_forall_ne hf _ hy]

/-- Key mapping sends disjoint union to disjoint union. -/
theorem mapKeys_union {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Γ Δ : Context Atom}
    (hdisj : Finmap.Disjoint Γ Δ) :
    (Γ ∪ Δ).mapKeys f hf = Γ.mapKeys f hf ∪ Δ.mapKeys f hf := by
  have _ := hdisj
  apply Finmap.ext_lookup
  intro y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [lookup_mapKeys_apply]
    by_cases hx : x ∈ Γ
    · rw [Finmap.lookup_union_left hx,
        Finmap.lookup_union_left ((mem_mapKeys hf).mpr ⟨x, hx, rfl⟩), lookup_mapKeys_apply]
    · have hx' : f x ∉ Γ.mapKeys f hf := by
        rw [mem_mapKeys hf]
        rintro ⟨x', hx', he⟩
        exact hx (hf he ▸ hx')
      rw [Finmap.lookup_union_right hx, Finmap.lookup_union_right hx', lookup_mapKeys_apply]
  · simp only [not_exists] at hy
    have hy' : y ∉ Γ.mapKeys f hf := by
      rw [mem_mapKeys hf]
      rintro ⟨x, _, he⟩
      exact hy x he
    rw [lookup_mapKeys_of_forall_ne hf _ hy, Finmap.lookup_union_right hy',
      lookup_mapKeys_of_forall_ne hf _ hy]

/-- Key mapping by an injective renaming is injective on contexts. -/
theorem mapKeys_injective {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) :
    Function.Injective (fun Γ : Context Atom => Γ.mapKeys f hf) := by
  intro Γ Δ h
  apply Finmap.ext_lookup
  intro x
  have := congrArg (Finmap.lookup (f x)) h
  simp only [lookup_mapKeys_apply] at this
  exact this

/-- Disjointness is preserved by lifting both contexts. -/
theorem disjoint_lift {Γ Δ : Context Atom} (hdisj : Finmap.Disjoint Γ Δ) :
    Finmap.Disjoint Γ.lift Δ.lift := by
  intro y hyΓ hyΔ
  obtain ⟨x, hx, rfl⟩ := mem_lift.mp hyΓ
  obtain ⟨x', hx', he⟩ := mem_lift.mp hyΔ
  rw [liftName_injective 0 he] at hx'
  exact hdisj x hx hx'

/-- Fresh insertion at the same key cancels in a context equation. -/
theorem insert_cancel {Γ Δ : Context Atom} {k : PiCalculus.Name}
    {a b : Logic.CLL.Proposition Atom} (hΓ : k ∉ Γ) (hΔ : k ∉ Δ)
    (h : Γ.insert k a = Δ.insert k b) : Γ = Δ ∧ a = b := by
  refine ⟨?_, ?_⟩
  · apply Finmap.ext_lookup
    intro x
    by_cases hx : x = k
    · subst hx
      rw [Finmap.lookup_eq_none.mpr hΓ, Finmap.lookup_eq_none.mpr hΔ]
    · have := congrArg (Finmap.lookup x) h
      rwa [Finmap.lookup_insert_of_ne _ hx, Finmap.lookup_insert_of_ne _ hx] at this
  · have := congrArg (Finmap.lookup k) h
    rw [Finmap.lookup_insert, Finmap.lookup_insert] at this
    exact Option.some.inj this

/-- A key renaming that fixes every key of a context fixes the mapped
context. -/
theorem mapKeys_eq_self_of_fixes {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Γ : Context Atom}
    (h : ∀ k ∈ Γ, f k = k) : Γ.mapKeys f hf = Γ := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y ∈ Γ
  · conv_lhs => rw [← h y hy]
    rw [lookup_mapKeys_apply]
  · rw [Finmap.lookup_eq_none.mpr hy]
    apply Option.eq_none_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨x, rfl, hx⟩ := mem_lookup_mapKeys.mp hv
    have hxΓ : x ∈ Γ := Finmap.mem_iff.mpr ⟨v, hx⟩
    exact hy (by rw [h x hxΓ]; exact hxΓ)

/-- Lifting a context twice is lifting it once and then mapping its keys
at cutoff `1`. -/
theorem lift_lift (Γ : Context Atom) :
    Γ.lift.lift =
      Γ.lift.mapKeys (PiCalculus.liftName 1) (liftName_injective 1) := by
  simp only [Context.lift, Context.mapKeys_comp]
  exact mapKeys_congr liftName_one_comp_liftName_zero.symm Γ

/-- Exchanging the two innermost variables on a twice-lifted context is
the identity. -/
theorem mapKeys_swap_lift_lift (Γ : Context Atom) :
    Γ.lift.lift.mapKeys (PiCalculus.swapNameAt 0) swapNameAt_injective =
      Γ.lift.lift := by
  apply mapKeys_eq_self_of_fixes
  intro k hk
  obtain ⟨y, hy, rfl⟩ := mem_lift.mp hk
  obtain ⟨x, _, rfl⟩ := mem_lift.mp hy
  rcases x with n | i
  · rfl
  · simp only [PiCalculus.liftName, PiCalculus.swapNameAt, Nat.zero_le, ↓reduceIte,
      show i + 1 + 1 ≠ 0 by omega, show i + 1 + 1 ≠ 0 + 1 by omega]

/-! ## Typing transport -/

/-- Inserting disjoint fresh keys in either order gives the same
context. -/
theorem insert_insert_comm {Γ : Context Atom}
    {k₁ k₂ : PiCalculus.Name} {v₁ v₂ : Logic.CLL.Proposition Atom}
    (h12 : k₁ ≠ k₂) :
    (Γ.insert k₁ v₁).insert k₂ v₂ = (Γ.insert k₂ v₂).insert k₁ v₁ :=
  Finmap.insert_insert_of_ne _ h12

/-- A fresh key of a disjoint union can be inserted on either side. -/
theorem insert_union_comm {Γ Δ : Context Atom}
    (hdisj : Finmap.Disjoint Γ Δ) {k : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hkΔ : k ∉ Δ) :
    (Γ.insert k v) ∪ Δ = (Γ ∪ Δ).insert k v := by
  have _ := hdisj
  have _ := hkΔ
  exact Finmap.insert_union.symm

/-- The typing judgment is invariant under shifting de Bruijn variables
at or above any cutoff. -/
theorem HasType.liftAt {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) (c : ℕ) :
    HasType (Γ.mapKeys (PiCalculus.liftName c) (liftName_injective c))
      (p.liftAt c) := by
  rw [← Proc.rename_liftName]
  exact h.rename (liftName_injective c)

/-- The typing judgment is invariant under exchanging the two innermost
de Bruijn variables. -/
theorem HasType.swap {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) :
    HasType (Γ.mapKeys (PiCalculus.swapNameAt 0) swapNameAt_injective)
      (p.rename (PiCalculus.swapNameAt 0)) :=
  h.rename swapNameAt_injective

/-- A lifted name is never the innermost bound variable. -/
private theorem liftName_zero_ne_var_zero (x : PiCalculus.Name) :
    PiCalculus.liftName 0 x ≠ .var 0 := by
  rcases x with n | i
  · simp only [PiCalculus.liftName, ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, ne_eq, PiCalculus.Name.var.injEq]
    omega

/-- Lifting a renaming under a binder preserves injectivity. -/
private theorem liftRename_injective {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) : Function.Injective (liftRename f) := by
  intro a b h
  rcases a with n | _ | i <;> rcases b with m | _ | j <;> simp only [liftRename] at h
  · exact hf (liftName_injective 0 h)
  · exact absurd h (liftName_zero_ne_var_zero _)
  · cases hf (liftName_injective 0 h)
  · exact absurd h.symm (liftName_zero_ne_var_zero _)
  · rfl
  · exact absurd h.symm (liftName_zero_ne_var_zero _)
  · cases hf (liftName_injective 0 h)
  · exact absurd h (liftName_zero_ne_var_zero _)
  · rw [PiCalculus.Name.var.inj (hf (liftName_injective 0 h))]

/-- Lifting commutes with an injective key map. -/
private theorem lift_mapKeys {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) (Γ : Context Atom) :
    (Γ.mapKeys f hf).lift = Γ.lift.mapKeys (liftRename f) (liftRename_injective hf) := by
  simp only [Context.lift, Context.mapKeys_comp]
  refine mapKeys_congr ?_ Γ
  funext x
  exact (liftRename_liftName f x).symm

/-- The empty context maps to the empty context. -/
private theorem mapKeys_empty {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) : (∅ : Context Atom).mapKeys f hf = ∅ :=
  rfl

/-- A context whose keys lie in the range of an injective key map is the
image of some context. -/
private theorem exists_mapKeys_eq {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Γ : Context Atom} (h : ∀ y ∈ Γ, ∃ x, f x = y) :
    ∃ Γ₀ : Context Atom, Γ₀.mapKeys f hf = Γ := by
  have : Nonempty PiCalculus.Name := ⟨.var 0⟩
  let g := Function.invFun f
  have hkeys : ∀ k ∈ Γ.entries.keys, f (g k) = k :=
    fun k hk => Function.invFun_eq (h k (Finmap.mem_def.mpr hk))
  refine ⟨⟨Γ.entries.map (fun e => ⟨g e.1, e.2⟩), ?_⟩, ?_⟩
  · rw [← Multiset.nodup_keys]
    have hn : Γ.entries.keys.Nodup := Γ.nodupKeys.nodup_keys
    have hk : (Multiset.map (fun e : Σ _ : PiCalculus.Name, Logic.CLL.Proposition Atom =>
          (⟨g e.1, e.2⟩ : Σ _ : PiCalculus.Name, Logic.CLL.Proposition Atom)) Γ.entries).keys =
        Γ.entries.keys.map g := by
      simp only [Multiset.keys, Multiset.map_map, Function.comp_def]
    rw [hk]
    refine hn.map_on ?_
    intro a ha b hb hab
    rw [← hkeys a ha, ← hkeys b hb, hab]
  · apply Finmap.ext
    simp only [Context.mapKeys, Multiset.map_map, Function.comp_def]
    conv_rhs => rw [← Multiset.map_id Γ.entries]
    refine Multiset.map_congr rfl ?_
    intro e he
    rw [hkeys e.1 (Multiset.mem_map_of_mem _ he)]
    rfl

/-- Preimage of a fresh insertion under an injective key map. -/
private theorem eq_insert_of_mapKeys {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Δ Γ : Context Atom} {x : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hx : f x ∉ Γ)
    (h : Δ.mapKeys f hf = Γ.insert (f x) v) :
    ∃ Γ₀ : Context Atom, Δ = Γ₀.insert x v ∧ x ∉ Γ₀ ∧ Γ₀.mapKeys f hf = Γ := by
  obtain ⟨Γ₀, rfl⟩ := exists_mapKeys_eq hf (Γ := Γ) (by
    intro y hy
    have hy' : y ∈ Δ.mapKeys f hf := by
      rw [h, Finmap.mem_insert]
      exact Or.inr hy
    obtain ⟨x', _, hx'⟩ := (mem_mapKeys hf).mp hy'
    exact ⟨x', hx'⟩)
  refine ⟨Γ₀, mapKeys_injective hf (by simp only; rw [h, mapKeys_insert]), ?_, rfl⟩
  intro hx0
  exact hx ((mem_mapKeys hf).mpr ⟨x, hx0, rfl⟩)

/-- Preimage of a disjoint union under an injective key map. -/
private theorem eq_union_of_mapKeys {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) {Δ A B : Context Atom} (hd : Finmap.Disjoint A B)
    (h : Δ.mapKeys f hf = A ∪ B) :
    ∃ A₀ B₀ : Context Atom, Δ = A₀ ∪ B₀ ∧ Finmap.Disjoint A₀ B₀ ∧
      A₀.mapKeys f hf = A ∧ B₀.mapKeys f hf = B := by
  have hr : ∀ C : Context Atom, (∀ y ∈ C, y ∈ A ∪ B) → ∀ y ∈ C, ∃ x, f x = y := by
    intro C hC y hy
    have hy' : y ∈ Δ.mapKeys f hf := by
      rw [h]
      exact hC y hy
    obtain ⟨x', _, hx'⟩ := (mem_mapKeys hf).mp hy'
    exact ⟨x', hx'⟩
  obtain ⟨A₀, rfl⟩ := exists_mapKeys_eq hf (Γ := A)
    (hr A (fun y hy => Finmap.mem_union.mpr (Or.inl hy)))
  obtain ⟨B₀, rfl⟩ := exists_mapKeys_eq hf (Γ := B)
    (hr B (fun y hy => Finmap.mem_union.mpr (Or.inr hy)))
  have hd₀ : Finmap.Disjoint A₀ B₀ := by
    intro x hxA hxB
    exact hd (f x) ((mem_mapKeys hf).mpr ⟨x, hxA, rfl⟩) ((mem_mapKeys hf).mpr ⟨x, hxB, rfl⟩)
  refine ⟨A₀, B₀, mapKeys_injective hf (by simp only; rw [h, mapKeys_union hf hd₀]), hd₀,
    rfl, rfl⟩

/-- Typing reflects injective renaming: a renamed process typed in a
key-mapped environment is typed in the original environment. -/
private theorem HasType.of_rename {Γ' : Context Atom} {p' : Proc Atom}
    (h : HasType Γ' p') :
    ∀ {f : PiCalculus.Name → PiCalculus.Name} (hf : Function.Injective f)
      {Δ : Context Atom} {p : Proc Atom},
      Δ.mapKeys f hf = Γ' → p.rename f = p' → HasType Δ p := by
  induction h with
  | @ax w x a hwx =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.link.injEq] at hr
    rename_i w₀ x₀
    obtain ⟨rfl, rfl⟩ := hr
    have hΔ' : Δ = ((∅ : Context Atom).insert w₀ a.dual).insert x₀ a :=
      mapKeys_injective hf (by simp only; rw [hΔ, mapKeys_insert, mapKeys_insert, mapKeys_empty])
    subst hΔ'
    exact HasType.ax (fun he => hwx (by rw [he]))
  | @cut Γ Δ' a p q hp hq hdisj ihp ihq =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.cut.injEq] at hr
    rename_i a₀ p₀ q₀
    obtain ⟨rfl, rfl, rfl⟩ := hr
    obtain ⟨A₀, B₀, rfl, hd, rfl, rfl⟩ := eq_union_of_mapKeys hf hdisj hΔ
    exact HasType.cut
      (ihp (liftRename_injective hf) (by rw [mapKeys_insert, ← lift_mapKeys]; rfl) rfl)
      (ihq (liftRename_injective hf) (by rw [mapKeys_insert, ← lift_mapKeys]; rfl) rfl) hd
  | @tensor Γ Δ' x a b p q hp hq hdisj hxΓ hxΔ ihp ihq =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.output.injEq] at hr
    rename_i x₀ p₀ q₀
    obtain ⟨rfl, rfl, rfl⟩ := hr
    have hx : f x₀ ∉ Γ ∪ Δ' := by
      rw [Finmap.mem_union]
      rintro (h | h)
      · exact hxΓ h
      · exact hxΔ h
    obtain ⟨E, rfl, hxE, hE⟩ := eq_insert_of_mapKeys hf hx hΔ
    obtain ⟨A₀, B₀, rfl, hd, rfl, rfl⟩ := eq_union_of_mapKeys hf hdisj hE
    rw [Finmap.mem_union, not_or] at hxE
    exact HasType.tensor
      (ihp (liftRename_injective hf) (by rw [mapKeys_insert, ← lift_mapKeys]; rfl) rfl)
      (ihq hf (by rw [mapKeys_insert]) rfl) hd hxE.1 hxE.2
  | @parr Γ x a b p hp hxΓ ih =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.input.injEq] at hr
    rename_i x₀ p₀
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨E, rfl, hxE, rfl⟩ := eq_insert_of_mapKeys hf hxΓ hΔ
    exact HasType.parr
      (ih (liftRename_injective hf)
        (by rw [mapKeys_insert, mapKeys_insert, ← lift_mapKeys, liftRename_liftName]; rfl) rfl)
      hxE
  | @oplusLeft Γ x a b p hp hxΓ ih =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.selectLeft.injEq] at hr
    rename_i x₀ p₀
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨E, rfl, hxE, rfl⟩ := eq_insert_of_mapKeys hf hxΓ hΔ
    exact HasType.oplusLeft (ih hf (by rw [mapKeys_insert]) rfl) hxE
  | @oplusRight Γ x a b p hp hxΓ ih =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.selectRight.injEq] at hr
    rename_i x₀ p₀
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨E, rfl, hxE, rfl⟩ := eq_insert_of_mapKeys hf hxΓ hΔ
    exact HasType.oplusRight (ih hf (by rw [mapKeys_insert]) rfl) hxE
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.choice.injEq] at hr
    rename_i x₀ p₀ q₀
    obtain ⟨rfl, rfl, rfl⟩ := hr
    obtain ⟨E, rfl, hxE, rfl⟩ := eq_insert_of_mapKeys hf hxΓ hΔ
    exact HasType.with (ihp hf (by rw [mapKeys_insert]) rfl)
      (ihq hf (by rw [mapKeys_insert]) rfl) hxE
  | @one x =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.emptyOutput.injEq] at hr
    rename_i x₀
    subst hr
    have hΔ' : Δ = (∅ : Context Atom).insert x₀ .one :=
      mapKeys_injective hf (by simp only; rw [hΔ, mapKeys_insert, mapKeys_empty])
    subst hΔ'
    exact HasType.one
  | @bot Γ x p hp hxΓ ih =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.emptyInput.injEq] at hr
    rename_i x₀ p₀
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨E, rfl, hxE, rfl⟩ := eq_insert_of_mapKeys hf hxΓ hΔ
    exact HasType.bot (ih hf rfl rfl) hxE
  | @top Γ x hxΓ =>
    intro f hf Δ r hΔ hr
    cases r <;> simp only [Proc.rename, reduceCtorEq, Proc.emptyChoice.injEq] at hr
    rename_i x₀
    subst hr
    obtain ⟨E, rfl, hxE, rfl⟩ := eq_insert_of_mapKeys hf hxΓ hΔ
    exact HasType.top hxE

/-- Retyping a lifted process back under a lowered environment
(strengthening at a general cutoff). -/
theorem HasType.lowering {Δ : Context Atom} {p : Proc Atom} (c : ℕ)
    (h :
      HasType
        (Δ.mapKeys (PiCalculus.liftName c) (liftName_injective c))
        (p.liftAt c)) :
    HasType Δ p :=
  HasType.of_rename h (liftName_injective c) rfl (Proc.rename_liftName c p)

/-! ## Structural equivalence -/

/-- Whether a process can take on a channel it does not use: a `⊤`
(`emptyChoice`) is reachable through some component of every cut and
output, and through both branches of every choice. -/
def Proc.absorbs : Proc Atom → Bool
  | .link _ _ => false
  | .cut _ p q => p.absorbs || q.absorbs
  | .output _ p q => p.absorbs || q.absorbs
  | .input _ p => p.absorbs
  | .selectLeft _ p => p.absorbs
  | .selectRight _ p => p.absorbs
  | .choice _ p q => p.absorbs && q.absorbs
  | .emptyOutput _ => false
  | .emptyInput _ p => p.absorbs
  | .emptyChoice _ => true

/-- Structural equivalence of classical processes: the equivalence
generated by cut symmetry and cut associativity. Associativity requires
that the middle component `q` can own both cut channels: each is free in
`q`, or `q` absorbs. This matches Figure 2's derivation-level side
condition up to re-derivation: on a typed instance it holds exactly when
some typing derivation assigns both channels to `q`
(`HasType.insert_iff_absorbs`, `Cong.assoc_of_hasType`). Without it,
associativity falsifies preservation (the `CongBare` counterexample in
the tests). -/
inductive Cong : Proc Atom → Proc Atom → Prop where
  | refl (p : Proc Atom) : Cong p p
  | symm {p q : Proc Atom} (h : Cong p q) : Cong q p
  | trans {p q r : Proc Atom} (h₁ : Cong p q) (h₂ : Cong q r) : Cong p r
  | swap (a : Logic.CLL.Proposition Atom) (p q : Proc Atom) :
      Cong (.cut a p q) (.cut a.dual q p)
  | assoc (a b : Logic.CLL.Proposition Atom) (p q r : Proc Atom)
      (hy : PiCalculus.Name.var 1 ∈ q.freeNames ∨ q.absorbs = true)
      (hx : PiCalculus.Name.var 0 ∈ q.freeNames ∨ q.absorbs = true) :
      Cong (.cut b (.cut a (p.liftAt 1) q) r)
        (.cut a p (.cut b (q.rename (PiCalculus.swapNameAt 0))
          (r.liftAt 1)))

/-- Lifting a context distributes over a disjoint union. -/
private theorem lift_union {A B : Context Atom} (h : Finmap.Disjoint A B) :
    (A ∪ B).lift = A.lift ∪ B.lift :=
  mapKeys_union _ h

/-- Lifting a context distributes over insertion. -/
private theorem lift_insert {Γ : Context Atom} {k : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} :
    Context.lift (Γ.insert k v) = Γ.lift.insert (PiCalculus.liftName 0 k) v :=
  mapKeys_insert _

/-- The second bound variable is in a lifted context exactly when the first
one is in the original context. -/
private theorem var_one_mem_lift {Γ : Context Atom}
    (h : PiCalculus.Name.var 1 ∈ Γ.lift) : PiCalculus.Name.var 0 ∈ Γ := by
  obtain ⟨x, hx, he⟩ := mem_lift.mp h
  rcases x with n | _ | i
  · simp only [PiCalculus.liftName, reduceCtorEq] at he
  · exact hx
  · simp only [PiCalculus.liftName, Nat.zero_le, ↓reduceIte, PiCalculus.Name.var.injEq] at he
    omega

/-- Insertion on the right of a union whose left part avoids the key. -/
private theorem union_insert_right {X Y : Context Atom} {k : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hk : k ∉ X) :
    X ∪ Y.insert k v = (X ∪ Y).insert k v := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = k
  · subst hx
    rw [Finmap.lookup_union_right hk, Finmap.lookup_insert, Finmap.lookup_insert]
  · rw [Finmap.lookup_insert_of_ne _ hx]
    by_cases hxX : x ∈ X
    · rw [Finmap.lookup_union_left hxX, Finmap.lookup_union_left hxX]
    · rw [Finmap.lookup_union_right hxX, Finmap.lookup_union_right hxX,
        Finmap.lookup_insert_of_ne _ hx]

/-- Inversion of the cut rule at an arbitrary environment. -/
private theorem HasType.cut_inv {C : Context Atom} {a : Logic.CLL.Proposition Atom}
    {p q : Proc Atom} (h : HasType C (.cut a p q)) :
    ∃ X Y : Context Atom, C = X ∪ Y ∧ HasType (X.lift.insert (.var 0) a) p ∧
      HasType (Y.lift.insert (.var 0) a.dual) q ∧ Finmap.Disjoint X Y := by
  cases h with
  | cut hp hq hd => exact ⟨_, _, rfl, hp, hq, hd⟩

/-- Key ownership in a cut premise: if the bound cut channel belongs to the
right part of a disjoint split of `G.lift.insert (var 0) b`, both parts
are lifts and the right part carries the channel. -/
private theorem split_cut_context {G X Y : Context Atom} {b : Logic.CLL.Proposition Atom}
    (hc : G.lift.insert (.var 0) b = X ∪ Y) (hd : Finmap.Disjoint X Y)
    (hy : PiCalculus.Name.var 0 ∈ Y) :
    ∃ X₀ Y₀ : Context Atom, X = X₀.lift ∧ Y = Y₀.lift.insert (.var 0) b ∧
      G = X₀ ∪ Y₀ ∧ Finmap.Disjoint X₀ Y₀ := by
  have hx0 : PiCalculus.Name.var 0 ∉ X := fun h => hd _ h hy
  obtain ⟨X₀, rfl⟩ := exists_unlift hx0
  have hlk : Y.lookup (.var 0) = some b := by
    have := congrArg (Finmap.lookup (PiCalculus.Name.var 0)) hc
    rw [Finmap.lookup_insert, Finmap.lookup_union_right hx0] at this
    exact this.symm
  have hY : Y = (Y.erase (.var 0)).insert (.var 0) b := by
    apply Finmap.ext_lookup
    intro x
    by_cases hx : x = .var 0
    · subst hx
      rw [hlk, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hx, Finmap.lookup_erase_ne hx]
  obtain ⟨Y₀, hY₀⟩ := exists_unlift (Γ := Y.erase (.var 0))
    (fun h => (Finmap.mem_erase.mp h).1 rfl)
  rw [← hY₀] at hY
  subst hY
  have hd₀ : Finmap.Disjoint X₀ Y₀ := by
    intro x hxX hxY
    refine hd (PiCalculus.liftName 0 x) (mem_lift.mpr ⟨x, hxX, rfl⟩) ?_
    rw [Finmap.mem_insert]
    exact Or.inr (mem_lift.mpr ⟨x, hxY, rfl⟩)
  refine ⟨X₀, Y₀, rfl, rfl, ?_, hd₀⟩
  apply mapKeys_injective (liftName_injective 0)
  change G.lift = (X₀ ∪ Y₀).lift
  rw [lift_union hd₀]
  have hc' := hc
  rw [union_insert_right hx0] at hc'
  exact (insert_cancel (var_zero_not_mem_lift G)
    (fun h => by
      rw [Finmap.mem_union] at h
      exact h.elim (var_zero_not_mem_lift X₀) (var_zero_not_mem_lift Y₀)) hc').1

/-- Renaming by the identity is the identity. -/
private theorem Proc.rename_id (p : Proc Atom) : p.rename id = p := by
  have hl : liftRename id = id := by
    funext x
    rcases x with n | _ | i <;> rfl
  induction p with
  | link x y => rfl
  | cut a p q ihp ihq => simp only [Proc.rename, hl, ihp, ihq]
  | output x p q ihp ihq => simp only [Proc.rename, hl, ihp, ihq, id]
  | input x p ih => simp only [Proc.rename, hl, ih, id]
  | selectLeft x p ih => simp only [Proc.rename, ih, id]
  | selectRight x p ih => simp only [Proc.rename, ih, id]
  | choice x p q ihp ihq => simp only [Proc.rename, ihp, ihq, id]
  | emptyOutput x => rfl
  | emptyInput x p ih => simp only [Proc.rename, ih, id]
  | emptyChoice x => rfl

/-- Cut symmetry preserves typing. -/
private theorem HasType.cut_swap {Γ : Context Atom} {a : Logic.CLL.Proposition Atom}
    {p q : Proc Atom} (h : HasType Γ (.cut a p q)) : HasType Γ (.cut a.dual q p) := by
  obtain ⟨X, Y, rfl, hp, hq, hd⟩ := h.cut_inv
  rw [Finmap.union_comm_of_disjoint hd]
  refine HasType.cut hq ?_ (Finmap.Disjoint.symm _ _ hd)
  rw [Logic.CLL.Proposition.dual_involution]
  exact hp

/-! ### Channels held only by `⊤`

A typed process that does not use a channel in its environment holds it
only through `⊤`, and can drop it; a process that `absorbs` can take on a
fresh channel. Together they move a cut channel between the components of
a cut or tensor premise, which is what derivation-level ownership allows. -/

/-- Absorption does not depend on channel names. -/
private theorem Proc.absorbs_rename (f : PiCalculus.Name → PiCalculus.Name) (p : Proc Atom) :
    (p.rename f).absorbs = p.absorbs := by
  induction p generalizing f with
  | link => rfl
  | cut _ _ _ ihp ihq => simp only [Proc.rename, Proc.absorbs, ihp, ihq]
  | output _ _ _ ihp ihq => simp only [Proc.rename, Proc.absorbs, ihp, ihq]
  | input _ _ ih => simp only [Proc.rename, Proc.absorbs, ih]
  | selectLeft _ _ ih => simp only [Proc.rename, Proc.absorbs, ih]
  | selectRight _ _ ih => simp only [Proc.rename, Proc.absorbs, ih]
  | choice _ _ _ ihp ihq => simp only [Proc.rename, Proc.absorbs, ihp, ihq]
  | emptyOutput => rfl
  | emptyInput _ _ ih => simp only [Proc.rename, Proc.absorbs, ih]
  | emptyChoice => rfl

/-- A name is free at depth zero in itself. -/
private theorem mem_freeNameAt_zero (x : PiCalculus.Name) : x ∈ freeNameAt 0 x := by
  rcases x with n | i
  · simp only [freeNameAt, Finset.mem_singleton]
  · simp only [freeNameAt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Finset.mem_singleton]

/-- A name is free under one more binder exactly when its lift is free. -/
private theorem mem_freeNameAt_succ (d : ℕ) (x y : PiCalculus.Name) :
    y ∈ freeNameAt (d + 1) x ↔ PiCalculus.liftName 0 y ∈ freeNameAt d x := by
  rcases x with n | i <;> rcases y with m | j
  · simp only [freeNameAt, PiCalculus.liftName]
  · simp only [freeNameAt, PiCalculus.liftName, Nat.zero_le, ↓reduceIte, Finset.mem_singleton,
      reduceCtorEq]
  · simp only [freeNameAt, PiCalculus.liftName]
    split_ifs <;> simp only [Finset.notMem_empty, Finset.mem_singleton, reduceCtorEq]
  · simp only [freeNameAt, PiCalculus.liftName, Nat.zero_le, ↓reduceIte]
    split_ifs <;>
      simp only [Finset.notMem_empty, Finset.mem_singleton, PiCalculus.Name.var.injEq,
        false_iff, iff_false] <;> omega

/-- A name is free in a process under one more binder exactly when its
lift is free. -/
private theorem mem_freeNamesAt_succ (p : Proc Atom) (d : ℕ) (y : PiCalculus.Name) :
    y ∈ p.freeNamesAt (d + 1) ↔ PiCalculus.liftName 0 y ∈ p.freeNamesAt d := by
  induction p generalizing d with
  | link x z => simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ]
  | cut _ _ _ ihp ihq => simp only [Proc.freeNamesAt, Finset.mem_union, ihp, ihq]
  | output x _ _ ihp ihq =>
    simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ, ihp, ihq]
  | input x _ ih => simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ, ih]
  | selectLeft x _ ih =>
    simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ, ih]
  | selectRight x _ ih =>
    simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ, ih]
  | choice x _ _ ihp ihq =>
    simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ, ihp, ihq]
  | emptyOutput x => simp only [Proc.freeNamesAt, mem_freeNameAt_succ]
  | emptyInput x _ ih =>
    simp only [Proc.freeNamesAt, Finset.mem_union, mem_freeNameAt_succ, ih]
  | emptyChoice x => simp only [Proc.freeNamesAt, mem_freeNameAt_succ]

/-- Lifting at a cutoff removes the variable at that cutoff from a name. -/
private theorem var_not_mem_freeNameAt_liftName (x : PiCalculus.Name) {c d e : ℕ}
    (he : e = c + d) : PiCalculus.Name.var c ∉ freeNameAt d (PiCalculus.liftName e x) := by
  subst he
  rcases x with n | i
  · simp only [PiCalculus.liftName, freeNameAt, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true]
  · simp only [PiCalculus.liftName]
    split_ifs <;>
      simp only [freeNameAt] <;> split_ifs <;>
        simp only [Finset.notMem_empty, Finset.mem_singleton, PiCalculus.Name.var.injEq,
          not_false_eq_true] <;> omega

/-- Lifting at a cutoff removes the variable at that cutoff from a process. -/
private theorem var_not_mem_freeNamesAt_liftAt (p : Proc Atom) (c : ℕ) :
    ∀ {d e : ℕ}, e = c + d → PiCalculus.Name.var c ∉ (p.liftAt e).freeNamesAt d := by
  induction p with
  | link x z =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨var_not_mem_freeNameAt_liftName x he, var_not_mem_freeNameAt_liftName z he⟩
  | cut _ _ _ ihp ihq =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨ihp (by omega), ihq (by omega)⟩
  | output x _ _ ihp ihq =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨⟨var_not_mem_freeNameAt_liftName x he, ihp (by omega)⟩, ihq he⟩
  | input x _ ih =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨var_not_mem_freeNameAt_liftName x he, ih (by omega)⟩
  | selectLeft x _ ih =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨var_not_mem_freeNameAt_liftName x he, ih he⟩
  | selectRight x _ ih =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨var_not_mem_freeNameAt_liftName x he, ih he⟩
  | choice x _ _ ihp ihq =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨⟨var_not_mem_freeNameAt_liftName x he, ihp he⟩, ihq he⟩
  | emptyOutput x =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt]
    exact var_not_mem_freeNameAt_liftName x he
  | emptyInput x _ ih =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt, Finset.mem_union, not_or]
    exact ⟨var_not_mem_freeNameAt_liftName x he, ih he⟩
  | emptyChoice x =>
    intro d e he
    simp only [Proc.liftAt, Proc.freeNamesAt]
    exact var_not_mem_freeNameAt_liftName x he

/-- The variable at a lifting cutoff is not free in the lifted process. -/
private theorem var_not_mem_freeNames_liftAt (p : Proc Atom) (c : ℕ) :
    PiCalculus.Name.var c ∉ (p.liftAt c).freeNames :=
  var_not_mem_freeNamesAt_liftAt p c (d := 0) rfl

/-- A name avoiding the variable at a lifting cutoff is a lift at that
cutoff. -/
private theorem exists_liftName_of_not_mem {x : PiCalculus.Name} {c d e : ℕ} (he : e = c + d)
    (h : PiCalculus.Name.var c ∉ freeNameAt d x) : ∃ x₀, x = PiCalculus.liftName e x₀ := by
  subst he
  rcases x with n | i
  · exact ⟨.const n, rfl⟩
  · by_cases hi : i < c + d
    · refine ⟨.var i, ?_⟩
      simp only [PiCalculus.liftName, show ¬ c + d ≤ i by omega, ↓reduceIte]
    · have hne : i ≠ c + d := by
        intro hic
        apply h
        simp only [freeNameAt, show ¬ i < d by omega, ↓reduceIte, Finset.mem_singleton,
          PiCalculus.Name.var.injEq]
        omega
      refine ⟨.var (i - 1), ?_⟩
      simp only [PiCalculus.liftName, show c + d ≤ i - 1 by omega, ↓reduceIte,
        PiCalculus.Name.var.injEq]
      omega

/-- A process in which the variable at a lifting cutoff is not free is a
lift at that cutoff. -/
private theorem exists_liftAt_of_not_mem (p : Proc Atom) (c : ℕ) :
    ∀ {d e : ℕ}, e = c + d → PiCalculus.Name.var c ∉ p.freeNamesAt d →
      ∃ p₀ : Proc Atom, p = p₀.liftAt e := by
  induction p with
  | link x z =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1
    obtain ⟨z₀, rfl⟩ := exists_liftName_of_not_mem he h.2
    exact ⟨.link x₀ z₀, rfl⟩
  | cut a _ _ ihp ihq =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨p₀, rfl⟩ := ihp (d := d + 1) (e := e + 1) (by omega) h.1
    obtain ⟨q₀, rfl⟩ := ihq (d := d + 1) (e := e + 1) (by omega) h.2
    exact ⟨.cut a p₀ q₀, rfl⟩
  | output x _ _ ihp ihq =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1.1
    obtain ⟨p₀, rfl⟩ := ihp (d := d + 1) (e := e + 1) (by omega) h.1.2
    obtain ⟨q₀, rfl⟩ := ihq he h.2
    exact ⟨.output x₀ p₀ q₀, rfl⟩
  | input x _ ih =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1
    obtain ⟨p₀, rfl⟩ := ih (d := d + 1) (e := e + 1) (by omega) h.2
    exact ⟨.input x₀ p₀, rfl⟩
  | selectLeft x _ ih =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1
    obtain ⟨p₀, rfl⟩ := ih he h.2
    exact ⟨.selectLeft x₀ p₀, rfl⟩
  | selectRight x _ ih =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1
    obtain ⟨p₀, rfl⟩ := ih he h.2
    exact ⟨.selectRight x₀ p₀, rfl⟩
  | choice x _ _ ihp ihq =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1.1
    obtain ⟨p₀, rfl⟩ := ihp he h.1.2
    obtain ⟨q₀, rfl⟩ := ihq he h.2
    exact ⟨.choice x₀ p₀ q₀, rfl⟩
  | emptyOutput x =>
    intro d e he h
    simp only [Proc.freeNamesAt] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h
    exact ⟨.emptyOutput x₀, rfl⟩
  | emptyInput x _ ih =>
    intro d e he h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h.1
    obtain ⟨p₀, rfl⟩ := ih he h.2
    exact ⟨.emptyInput x₀ p₀, rfl⟩
  | emptyChoice x =>
    intro d e he h
    simp only [Proc.freeNamesAt] at h
    obtain ⟨x₀, rfl⟩ := exists_liftName_of_not_mem he h
    exact ⟨.emptyChoice x₀, rfl⟩

/-- Erasing a key commutes with inserting a different key. -/
private theorem erase_insert_of_ne {C : Context Atom} {k k' : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (h : k ≠ k') :
    (C.insert k' v).erase k = (C.erase k).insert k' v := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = k
  · subst hy
    rw [Finmap.lookup_erase, Finmap.lookup_insert_of_ne _ h, Finmap.lookup_erase]
  · rw [Finmap.lookup_erase_ne hy]
    by_cases hy' : y = k'
    · subst hy'
      rw [Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hy', Finmap.lookup_insert_of_ne _ hy',
        Finmap.lookup_erase_ne hy]

/-- Erasing a key distributes over a union. -/
private theorem erase_union {A B : Context Atom} (k : PiCalculus.Name) :
    (A ∪ B).erase k = A.erase k ∪ B.erase k := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = k
  · subst hy
    rw [Finmap.lookup_erase, Finmap.lookup_union_right (fun h => (Finmap.mem_erase.mp h).1 rfl),
      Finmap.lookup_erase]
  · rw [Finmap.lookup_erase_ne hy]
    by_cases hA : y ∈ A
    · rw [Finmap.lookup_union_left hA, Finmap.lookup_union_left (Finmap.mem_erase.mpr ⟨hy, hA⟩),
        Finmap.lookup_erase_ne hy]
    · rw [Finmap.lookup_union_right hA,
        Finmap.lookup_union_right (fun h => hA (Finmap.mem_erase.mp h).2),
        Finmap.lookup_erase_ne hy]

/-- Erasing an absent key changes nothing. -/
private theorem erase_of_not_mem {C : Context Atom} {k : PiCalculus.Name} (h : k ∉ C) :
    C.erase k = C := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = k
  · subst hy
    rw [Finmap.lookup_erase, Finmap.lookup_eq_none.mpr h]
  · rw [Finmap.lookup_erase_ne hy]

/-- Lifting commutes with erasing a key. -/
private theorem lift_erase (C : Context Atom) (k : PiCalculus.Name) :
    Context.lift (C.erase k) = C.lift.erase (PiCalculus.liftName 0 k) := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : ∃ x, PiCalculus.liftName 0 x = y
  · obtain ⟨x, rfl⟩ := hy
    have e₁ : (Context.lift (C.erase k)).lookup (PiCalculus.liftName 0 x) =
        (C.erase k).lookup x := lookup_mapKeys_apply _ _ x
    have e₂ : C.lift.lookup (PiCalculus.liftName 0 x) = C.lookup x :=
      lookup_mapKeys_apply _ _ x
    rw [e₁]
    by_cases hx : x = k
    · subst hx
      rw [Finmap.lookup_erase, Finmap.lookup_erase]
    · rw [Finmap.lookup_erase_ne hx,
        Finmap.lookup_erase_ne (fun h => hx (liftName_injective 0 h)), e₂]
  · have hy' : ∀ x, PiCalculus.liftName 0 x ≠ y := fun x hx => hy ⟨x, hx⟩
    have e₁ : (Context.lift (C.erase k)).lookup y = none :=
      lookup_mapKeys_of_forall_ne _ _ hy'
    have e₂ : C.lift.lookup y = none := lookup_mapKeys_of_forall_ne _ _ hy'
    rw [e₁, Finmap.lookup_erase_ne (fun h => hy' k h.symm), e₂]

/-- Erasing a key keeps two contexts disjoint. -/
private theorem disjoint_erase {A B : Context Atom} (h : Finmap.Disjoint A B)
    (k : PiCalculus.Name) : Finmap.Disjoint (A.erase k) (B.erase k) :=
  fun y hA hB => h y (Finmap.mem_erase.mp hA).2 (Finmap.mem_erase.mp hB).2

/-- Moving one key from the left part of a disjoint split to the right. -/
private theorem disjoint_erase_insert {X Y : Context Atom} {k : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (h : Finmap.Disjoint X Y) :
    Finmap.Disjoint (X.erase k) (Y.insert k v) := by
  intro y hy hyY
  rw [Finmap.mem_erase] at hy
  rw [Finmap.mem_insert] at hyY
  rcases hyY with rfl | hyY
  · exact hy.1 rfl
  · exact h y hy.2 hyY

/-- A fresh key keeps an insertion disjoint on the left. -/
private theorem disjoint_insert_fresh {G R : Context Atom} {x : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hx : x ∉ R) (h : Finmap.Disjoint G R) :
    Finmap.Disjoint (G.insert x v) R := by
  intro k hk hkR
  rw [Finmap.mem_insert] at hk
  rcases hk with rfl | hk
  · exact hx hkR
  · exact h k hk hkR

/-- Moving a key from the left part of a union to the right part. -/
private theorem union_move_right {X Y : Context Atom} {k : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hk : k ∈ X) (hv : X.lookup k = some v) :
    X ∪ Y = X.erase k ∪ Y.insert k v := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = k
  · subst hy
    rw [Finmap.lookup_union_left hk, hv,
      Finmap.lookup_union_right (fun h => (Finmap.mem_erase.mp h).1 rfl), Finmap.lookup_insert]
  · by_cases hyX : y ∈ X
    · rw [Finmap.lookup_union_left hyX, Finmap.lookup_union_left (Finmap.mem_erase.mpr ⟨hy, hyX⟩),
        Finmap.lookup_erase_ne hy]
    · rw [Finmap.lookup_union_right hyX,
        Finmap.lookup_union_right (fun h => hyX (Finmap.mem_erase.mp h).2),
        Finmap.lookup_insert_of_ne _ hy]

/-- Moving a key from the right part of a union to the left part. -/
private theorem union_move_left {X Y : Context Atom} {k : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hk : k ∈ Y) (hv : Y.lookup k = some v) (hkX : k ∉ X) :
    X ∪ Y = X.insert k v ∪ Y.erase k := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = k
  · subst hy
    rw [Finmap.lookup_union_right hkX, hv,
      Finmap.lookup_union_left (Finmap.mem_insert.mpr (Or.inl rfl)), Finmap.lookup_insert]
  · have _ := hk
    by_cases hyX : y ∈ X
    · rw [Finmap.lookup_union_left hyX,
        Finmap.lookup_union_left (Finmap.mem_insert.mpr (Or.inr hyX)),
        Finmap.lookup_insert_of_ne _ hy]
    · rw [Finmap.lookup_union_right hyX,
        Finmap.lookup_union_right (by rw [Finmap.mem_insert, not_or]; exact ⟨hy, hyX⟩),
        Finmap.lookup_erase_ne hy]

/-- A fresh name lifts to a name outside a lifted cut premise. -/
private theorem liftName_not_mem_lift_insert {Γ : Context Atom} {k : PiCalculus.Name}
    {a : Logic.CLL.Proposition Atom} (hk : k ∉ Γ) :
    PiCalculus.liftName 0 k ∉ Γ.lift.insert (.var 0) a := by
  rw [Finmap.mem_insert, not_or]
  refine ⟨liftName_zero_ne_var_zero k, fun h => hk ?_⟩
  obtain ⟨x, hx, he⟩ := mem_lift.mp h
  rwa [← liftName_injective 0 he]

/-- A channel a typed process does not use can be dropped from its
environment. -/
private theorem HasType.strengthen {C : Context Atom} {p : Proc Atom} (h : HasType C p) :
    ∀ {k : PiCalculus.Name}, k ∉ p.freeNames → HasType (C.erase k) p := by
  induction h with
  | @ax w x a hwx =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    rw [erase_of_not_mem]
    · exact HasType.ax hwx
    · rw [Finmap.mem_insert, Finmap.mem_insert, not_or, not_or]
      exact ⟨fun h => hk.2 (by rw [h]; exact mem_freeNameAt_zero x),
        fun h => hk.1 (by rw [h]; exact mem_freeNameAt_zero w), Finmap.notMem_empty⟩
  | @cut Γ Δ a p q hp hq hd ihp ihq =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hp' := ihp (k := PiCalculus.liftName 0 k)
      (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hk.1)
    have hq' := ihq (k := PiCalculus.liftName 0 k)
      (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hk.2)
    rw [erase_insert_of_ne (liftName_zero_ne_var_zero k), ← lift_erase] at hp' hq'
    rw [erase_union]
    exact HasType.cut hp' hq' (disjoint_erase hd k)
  | @tensor Γ Δ x a b p q hp hq hd hxΓ hxΔ ihp ihq =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hkx : k ≠ x := fun h => hk.1.1 (by rw [h]; exact mem_freeNameAt_zero x)
    have hp' := ihp (k := PiCalculus.liftName 0 k)
      (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hk.1.2)
    have hq' := ihq (k := k) hk.2
    rw [erase_insert_of_ne (liftName_zero_ne_var_zero k), ← lift_erase] at hp'
    rw [erase_insert_of_ne hkx] at hq'
    rw [erase_insert_of_ne hkx, erase_union]
    exact HasType.tensor hp' hq' (disjoint_erase hd k)
      (fun h => hxΓ (Finmap.mem_erase.mp h).2) (fun h => hxΔ (Finmap.mem_erase.mp h).2)
  | @parr Γ x a b p hp hxΓ ih =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hkx : k ≠ x := fun h => hk.1 (by rw [h]; exact mem_freeNameAt_zero x)
    have hp' := ih (k := PiCalculus.liftName 0 k)
      (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hk.2)
    rw [erase_insert_of_ne (fun h => hkx (liftName_injective 0 h)),
      erase_insert_of_ne (liftName_zero_ne_var_zero k), ← lift_erase] at hp'
    rw [erase_insert_of_ne hkx]
    exact HasType.parr hp' (fun h => hxΓ (Finmap.mem_erase.mp h).2)
  | @oplusLeft Γ x a b p hp hxΓ ih =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hkx : k ≠ x := fun h => hk.1 (by rw [h]; exact mem_freeNameAt_zero x)
    have hp' := ih (k := k) hk.2
    rw [erase_insert_of_ne hkx] at hp'
    rw [erase_insert_of_ne hkx]
    exact HasType.oplusLeft hp' (fun h => hxΓ (Finmap.mem_erase.mp h).2)
  | @oplusRight Γ x a b p hp hxΓ ih =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hkx : k ≠ x := fun h => hk.1 (by rw [h]; exact mem_freeNameAt_zero x)
    have hp' := ih (k := k) hk.2
    rw [erase_insert_of_ne hkx] at hp'
    rw [erase_insert_of_ne hkx]
    exact HasType.oplusRight hp' (fun h => hxΓ (Finmap.mem_erase.mp h).2)
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hkx : k ≠ x := fun h => hk.1.1 (by rw [h]; exact mem_freeNameAt_zero x)
    have hp' := ihp (k := k) hk.1.2
    have hq' := ihq (k := k) hk.2
    rw [erase_insert_of_ne hkx] at hp'
    rw [erase_insert_of_ne hkx] at hq'
    rw [erase_insert_of_ne hkx]
    exact HasType.«with» hp' hq' (fun h => hxΓ (Finmap.mem_erase.mp h).2)
  | @one x =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt] at hk
    rw [erase_of_not_mem]
    · exact HasType.one
    · rw [Finmap.mem_insert, not_or]
      exact ⟨fun h => hk (by rw [h]; exact mem_freeNameAt_zero x), Finmap.notMem_empty⟩
  | @bot Γ x p hp hxΓ ih =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hk
    have hkx : k ≠ x := fun h => hk.1 (by rw [h]; exact mem_freeNameAt_zero x)
    rw [erase_insert_of_ne hkx]
    exact HasType.bot (ih hk.2) (fun h => hxΓ (Finmap.mem_erase.mp h).2)
  | @top Γ x hxΓ =>
    intro k hk
    simp only [Proc.freeNames, Proc.freeNamesAt] at hk
    have hkx : k ≠ x := fun h => hk (by rw [h]; exact mem_freeNameAt_zero x)
    rw [erase_insert_of_ne hkx]
    exact HasType.top (fun h => hxΓ (Finmap.mem_erase.mp h).2)

/-- An absorbing typed process can take on one more fresh channel. -/
private theorem HasType.weaken_absorbs {C : Context Atom} {p : Proc Atom} (h : HasType C p) :
    p.absorbs = true → ∀ {k : PiCalculus.Name} {v : Logic.CLL.Proposition Atom},
      k ∉ C → HasType (C.insert k v) p := by
  induction h with
  | ax => intro habs; simp only [Proc.absorbs, Bool.false_eq_true] at habs
  | @cut Γ Δ a p q hp hq hd ihp ihq =>
    intro habs k v hk
    rw [Finmap.mem_union, not_or] at hk
    simp only [Proc.absorbs, Bool.or_eq_true] at habs
    rcases habs with habs | habs
    · have hp' := ihp habs (k := PiCalculus.liftName 0 k) (v := v)
        (liftName_not_mem_lift_insert hk.1)
      rw [insert_insert_comm (Ne.symm (liftName_zero_ne_var_zero k)), ← lift_insert] at hp'
      rw [← insert_union_comm hd hk.2]
      exact HasType.cut hp' hq (disjoint_insert_fresh hk.2 hd)
    · have hq' := ihq habs (k := PiCalculus.liftName 0 k) (v := v)
        (liftName_not_mem_lift_insert hk.2)
      rw [insert_insert_comm (Ne.symm (liftName_zero_ne_var_zero k)), ← lift_insert] at hq'
      rw [← union_insert_right hk.1]
      exact HasType.cut hp hq'
        (Finmap.Disjoint.symm _ _ (disjoint_insert_fresh hk.1 (Finmap.Disjoint.symm _ _ hd)))
  | @tensor Γ Δ x a b p q hp hq hd hxΓ hxΔ ihp ihq =>
    intro habs k v hk
    rw [Finmap.mem_insert, not_or, Finmap.mem_union, not_or] at hk
    obtain ⟨hkx, hkΓ, hkΔ⟩ := hk
    simp only [Proc.absorbs, Bool.or_eq_true] at habs
    rw [insert_insert_comm (Ne.symm hkx)]
    rcases habs with habs | habs
    · have hp' := ihp habs (k := PiCalculus.liftName 0 k) (v := v)
        (liftName_not_mem_lift_insert hkΓ)
      rw [insert_insert_comm (Ne.symm (liftName_zero_ne_var_zero k)), ← lift_insert] at hp'
      rw [← insert_union_comm hd hkΔ]
      exact HasType.tensor hp' hq (disjoint_insert_fresh hkΔ hd)
        (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hkx, hxΓ⟩) hxΔ
    · have hq' := ihq habs (k := k) (v := v)
        (by rw [Finmap.mem_insert, not_or]; exact ⟨hkx, hkΔ⟩)
      rw [insert_insert_comm (Ne.symm hkx)] at hq'
      rw [← union_insert_right hkΓ]
      exact HasType.tensor hp hq'
        (Finmap.Disjoint.symm _ _ (disjoint_insert_fresh hkΓ (Finmap.Disjoint.symm _ _ hd)))
        hxΓ (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hkx, hxΔ⟩)
  | @parr Γ x a b p hp hxΓ ih =>
    intro habs k v hk
    rw [Finmap.mem_insert, not_or] at hk
    obtain ⟨hkx, hkΓ⟩ := hk
    simp only [Proc.absorbs] at habs
    have hlx : PiCalculus.liftName 0 k ≠ PiCalculus.liftName 0 x :=
      fun h => hkx (liftName_injective 0 h)
    have hp' := ih habs (k := PiCalculus.liftName 0 k) (v := v) (by
      rw [Finmap.mem_insert, not_or]
      exact ⟨hlx, liftName_not_mem_lift_insert hkΓ⟩)
    rw [insert_insert_comm (Ne.symm hlx),
      insert_insert_comm (Ne.symm (liftName_zero_ne_var_zero k)), ← lift_insert] at hp'
    rw [insert_insert_comm (Ne.symm hkx)]
    exact HasType.parr hp' (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hkx, hxΓ⟩)
  | @oplusLeft Γ x a b p hp hxΓ ih =>
    intro habs k v hk
    rw [Finmap.mem_insert, not_or] at hk
    simp only [Proc.absorbs] at habs
    have hp' := ih habs (k := k) (v := v) (by rw [Finmap.mem_insert, not_or]; exact hk)
    rw [insert_insert_comm (Ne.symm hk.1)] at hp'
    rw [insert_insert_comm (Ne.symm hk.1)]
    exact HasType.oplusLeft hp' (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hk.1, hxΓ⟩)
  | @oplusRight Γ x a b p hp hxΓ ih =>
    intro habs k v hk
    rw [Finmap.mem_insert, not_or] at hk
    simp only [Proc.absorbs] at habs
    have hp' := ih habs (k := k) (v := v) (by rw [Finmap.mem_insert, not_or]; exact hk)
    rw [insert_insert_comm (Ne.symm hk.1)] at hp'
    rw [insert_insert_comm (Ne.symm hk.1)]
    exact HasType.oplusRight hp' (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hk.1, hxΓ⟩)
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
    intro habs k v hk
    rw [Finmap.mem_insert, not_or] at hk
    simp only [Proc.absorbs, Bool.and_eq_true] at habs
    have hp' := ihp habs.1 (k := k) (v := v) (by rw [Finmap.mem_insert, not_or]; exact hk)
    have hq' := ihq habs.2 (k := k) (v := v) (by rw [Finmap.mem_insert, not_or]; exact hk)
    rw [insert_insert_comm (Ne.symm hk.1)] at hp'
    rw [insert_insert_comm (Ne.symm hk.1)] at hq'
    rw [insert_insert_comm (Ne.symm hk.1)]
    exact HasType.«with» hp' hq' (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hk.1, hxΓ⟩)
  | one => intro habs; simp only [Proc.absorbs, Bool.false_eq_true] at habs
  | @bot Γ x p hp hxΓ ih =>
    intro habs k v hk
    rw [Finmap.mem_insert, not_or] at hk
    simp only [Proc.absorbs] at habs
    rw [insert_insert_comm (Ne.symm hk.1)]
    exact HasType.bot (ih habs hk.2)
      (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hk.1, hxΓ⟩)
  | @top Γ x hxΓ =>
    intro _ k v hk
    rw [Finmap.mem_insert, not_or] at hk
    rw [insert_insert_comm (Ne.symm hk.1)]
    exact HasType.top (by rw [Finmap.mem_insert, not_or]; exact ⟨Ne.symm hk.1, hxΓ⟩)

/-- A typed process that holds a channel it does not use absorbs. -/
private theorem HasType.absorbs_of_unused {C : Context Atom} {p : Proc Atom}
    (h : HasType C p) : ∀ {k : PiCalculus.Name}, k ∈ C → k ∉ p.freeNames →
      p.absorbs = true := by
  have lift_mem : ∀ {Γ : Context Atom} {k : PiCalculus.Name} {a : Logic.CLL.Proposition Atom},
      k ∈ Γ → PiCalculus.liftName 0 k ∈ Γ.lift.insert (.var 0) a :=
    fun hk => Finmap.mem_insert.mpr (Or.inr (mem_lift.mpr ⟨_, hk, rfl⟩))
  induction h with
  | @ax w x a hwx =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    rw [Finmap.mem_insert, Finmap.mem_insert] at hk
    rcases hk with rfl | rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.2
    · exact absurd (mem_freeNameAt_zero _) hkf.1
    · exact absurd hk Finmap.notMem_empty
  | @cut Γ Δ a p q hp hq hd ihp ihq =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs, Bool.or_eq_true]
    rcases Finmap.mem_union.mp hk with hk | hk
    · exact Or.inl (ihp (lift_mem hk) (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hkf.1))
    · exact Or.inr (ihq (lift_mem hk) (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hkf.2))
  | @tensor Γ Δ x a b p q hp hq hd hxΓ hxΔ ihp ihq =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs, Bool.or_eq_true]
    rw [Finmap.mem_insert, Finmap.mem_union] at hk
    rcases hk with rfl | hk | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.1.1
    · exact Or.inl (ihp (lift_mem hk)
        (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hkf.1.2))
    · exact Or.inr (ihq (Finmap.mem_insert.mpr (Or.inr hk)) hkf.2)
  | @parr Γ x a b p hp hxΓ ih =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs]
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.1
    · exact ih (Finmap.mem_insert.mpr (Or.inr (lift_mem hk)))
        (by rw [Proc.freeNames, ← mem_freeNamesAt_succ]; exact hkf.2)
  | @oplusLeft Γ x a b p hp hxΓ ih =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs]
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.1
    · exact ih (Finmap.mem_insert.mpr (Or.inr hk)) hkf.2
  | @oplusRight Γ x a b p hp hxΓ ih =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs]
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.1
    · exact ih (Finmap.mem_insert.mpr (Or.inr hk)) hkf.2
  | @«with» Γ x a b p q hp hq hxΓ ihp ihq =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs, Bool.and_eq_true]
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.1.1
    · exact ⟨ihp (Finmap.mem_insert.mpr (Or.inr hk)) hkf.1.2,
        ihq (Finmap.mem_insert.mpr (Or.inr hk)) hkf.2⟩
  | @one x =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt] at hkf
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf
    · exact absurd hk Finmap.notMem_empty
  | @bot Γ x p hp hxΓ ih =>
    intro k hk hkf
    simp only [Proc.freeNames, Proc.freeNamesAt, Finset.mem_union, not_or] at hkf
    simp only [Proc.absorbs]
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact absurd (mem_freeNameAt_zero _) hkf.1
    · exact ih hk hkf.2
  | top => intro _ _ _; rfl

/-- Absorption is exactly the ability of a typed process to carry one
more channel that it does not use. This is what lets the side conditions
of `Cong.assoc`, `Step.commTensorLeft` and `Step.commTensorRight` match
derivation-level channel ownership: a component can own a cut channel in
some derivation exactly when the channel is free in it or it absorbs. -/
theorem HasType.insert_iff_absorbs {C : Context Atom} {p : Proc Atom} (h : HasType C p)
    {k : PiCalculus.Name} (hkC : k ∉ C) (hkp : k ∉ p.freeNames)
    (v : Logic.CLL.Proposition Atom) :
    HasType (C.insert k v) p ↔ p.absorbs = true :=
  ⟨fun h' => h'.absorbs_of_unused (Finmap.mem_insert.mpr (Or.inl rfl)) hkp,
    fun habs => h.weaken_absorbs habs hkC⟩

/-- Move the outer cut channel of a cut premise from a component that
does not use it to an absorbing one. -/
private theorem rebalance_cut {G X Y : Context Atom} {b a a' : Logic.CLL.Proposition Atom}
    {P Q : Proc Atom} (hC : G.lift.insert (.var 0) b = X ∪ Y) (hXY : Finmap.Disjoint X Y)
    (h0 : PiCalculus.Name.var 0 ∈ X)
    (hP : HasType (X.lift.insert (.var 0) a) P) (hQ : HasType (Y.lift.insert (.var 0) a') Q)
    (hPf : PiCalculus.Name.var 1 ∉ P.freeNames) (hQa : Q.absorbs = true) :
    ∃ X' Y' : Context Atom, G.lift.insert (.var 0) b = X' ∪ Y' ∧
      HasType (X'.lift.insert (.var 0) a) P ∧ HasType (Y'.lift.insert (.var 0) a') Q ∧
      Finmap.Disjoint X' Y' ∧ PiCalculus.Name.var 0 ∈ Y' := by
  have h0Y : PiCalculus.Name.var 0 ∉ Y := fun h => hXY _ h0 h
  have hlk : X.lookup (.var 0) = some b := by
    have e := congrArg (Finmap.lookup (PiCalculus.Name.var 0)) hC
    rw [Finmap.lookup_insert, Finmap.lookup_union_left h0] at e
    exact e.symm
  have h1 : PiCalculus.Name.var 1 = PiCalculus.liftName 0 (.var 0) := rfl
  refine ⟨X.erase (.var 0), Y.insert (.var 0) b, ?_, ?_, ?_, disjoint_erase_insert hXY,
    Finmap.mem_insert.mpr (Or.inl rfl)⟩
  · rw [hC, union_move_right h0 hlk]
  · have hs := hP.strengthen hPf
    rwa [erase_insert_of_ne (by decide), h1, ← lift_erase] at hs
  · have hw := hQ.weaken_absorbs hQa (k := .var 1) (v := b) (by
      rw [Finmap.mem_insert, not_or]
      exact ⟨by decide, fun h => h0Y (var_one_mem_lift h)⟩)
    rwa [insert_insert_comm (by decide), h1, ← lift_insert] at hw

/-- Cut associativity, left-nested to right-nested, preserves typing when
the outer cut channel is free in, or absorbable by, the middle component. -/
private theorem HasType.assoc_fwd {Γ : Context Atom} {a b : Logic.CLL.Proposition Atom}
    {p q r : Proc Atom} (hy : PiCalculus.Name.var 1 ∈ q.freeNames ∨ q.absorbs = true)
    (h : HasType Γ (.cut b (.cut a (p.liftAt 1) q) r)) :
    HasType Γ (.cut a p (.cut b (q.rename (PiCalculus.swapNameAt 0)) (r.liftAt 1))) := by
  obtain ⟨G, R, rfl, hl, hr, hGR⟩ := h.cut_inv
  obtain ⟨X, Y, hC, hp, hq, hXY, hyY⟩ : ∃ X Y : Context Atom,
      G.lift.insert (.var 0) b = X ∪ Y ∧ HasType (X.lift.insert (.var 0) a) (p.liftAt 1) ∧
        HasType (Y.lift.insert (.var 0) a.dual) q ∧ Finmap.Disjoint X Y ∧
        PiCalculus.Name.var 0 ∈ Y := by
    obtain ⟨X, Y, hC, hp, hq, hXY⟩ := hl.cut_inv
    by_cases hyY : PiCalculus.Name.var 0 ∈ Y
    · exact ⟨X, Y, hC, hp, hq, hXY, hyY⟩
    rcases hy with hy | hy
    · have hk := HasType.freeNames_subset_keys hq hy
      rw [Finmap.mem_keys, Finmap.mem_insert] at hk
      rcases hk with hk | hk
      · simp only [PiCalculus.Name.var.injEq, Nat.one_ne_zero] at hk
      · exact absurd (var_one_mem_lift hk) hyY
    · have h0X : PiCalculus.Name.var 0 ∈ X := by
        have h0 : PiCalculus.Name.var 0 ∈ X ∪ Y := by
          rw [← hC]
          exact Finmap.mem_insert.mpr (Or.inl rfl)
        rcases Finmap.mem_union.mp h0 with h0 | h0
        · exact h0
        · exact absurd h0 hyY
      exact rebalance_cut hC hXY h0X hp hq (var_not_mem_freeNames_liftAt p 1) hy
  obtain ⟨P₀, Q₀, rfl, rfl, rfl, hPQ⟩ := split_cut_context hC hXY hyY
  rw [Finmap.disjoint_union_left] at hGR
  have hp' : HasType (P₀.lift.insert (.var 0) a) p :=
    HasType.lowering 1 (by rw [mapKeys_insert, ← lift_lift]; exact hp)
  have hq' : HasType
      ((Context.lift (Q₀.lift.insert (PiCalculus.Name.var 0) a.dual)).insert (.var 0) b)
      (q.rename (PiCalculus.swapNameAt 0)) := by
    have hs := HasType.swap hq
    rw [lift_insert, mapKeys_insert, mapKeys_insert, mapKeys_swap_lift_lift] at hs
    rw [lift_insert]
    convert hs using 1
    exact insert_insert_comm (by decide)
  have hr' : HasType (R.lift.lift.insert (.var 0) b.dual) (r.liftAt 1) := by
    have hl1 := HasType.liftAt hr 1
    rw [mapKeys_insert, ← lift_lift] at hl1
    exact hl1
  have hQR : Finmap.Disjoint (Q₀.lift.insert (.var 0) a.dual) R.lift := by
    intro k hk hkR
    rw [Finmap.mem_insert] at hk
    rcases hk with rfl | hk
    · exact var_zero_not_mem_lift R hkR
    · exact disjoint_lift hGR.2 k hk hkR
  have hin := HasType.cut hq' hr' hQR
  have hPQR : Finmap.Disjoint P₀ (Q₀ ∪ R) :=
    (Finmap.disjoint_union_right _ _ _).mpr ⟨hPQ, hGR.1⟩
  rw [Finmap.union_assoc]
  refine HasType.cut hp' ?_ hPQR
  rw [lift_union hGR.2, ← insert_union_comm (disjoint_lift hGR.2) (var_zero_not_mem_lift R)]
  exact hin

/-- Cut associativity, right-nested to left-nested, preserves typing when
the inner cut channel is free in, or absorbable by, the middle component. -/
private theorem HasType.assoc_bwd {Γ : Context Atom} {a b : Logic.CLL.Proposition Atom}
    {p q r : Proc Atom} (hx : PiCalculus.Name.var 0 ∈ q.freeNames ∨ q.absorbs = true)
    (h : HasType Γ (.cut a p (.cut b (q.rename (PiCalculus.swapNameAt 0)) (r.liftAt 1)))) :
    HasType Γ (.cut b (.cut a (p.liftAt 1) q) r) := by
  obtain ⟨P₀, D, rfl, hp, hD, hPD⟩ := h.cut_inv
  obtain ⟨X, Y, hC, hq', hr', hXY, hxX⟩ : ∃ X Y : Context Atom,
      D.lift.insert (.var 0) a.dual = X ∪ Y ∧
        HasType (X.lift.insert (.var 0) b) (q.rename (PiCalculus.swapNameAt 0)) ∧
        HasType (Y.lift.insert (.var 0) b.dual) (r.liftAt 1) ∧ Finmap.Disjoint X Y ∧
        PiCalculus.Name.var 0 ∈ X := by
    obtain ⟨X, Y, hC, hq', hr', hXY⟩ := hD.cut_inv
    by_cases hxX : PiCalculus.Name.var 0 ∈ X
    · exact ⟨X, Y, hC, hq', hr', hXY, hxX⟩
    rcases hx with hx | hx
    · have hq₀ : HasType (Context.mapKeys (PiCalculus.swapNameAt 0) swapNameAt_injective
          (X.lift.insert (PiCalculus.Name.var 0) b)) q := by
        have hs := HasType.swap hq'
        rwa [Proc.rename_comp, show PiCalculus.swapNameAt 0 ∘ PiCalculus.swapNameAt 0 = id from
          funext swapNameAt_involutive, Proc.rename_id] at hs
      have hk := HasType.freeNames_subset_keys hq₀ hx
      rw [Finmap.mem_keys, mem_mapKeys] at hk
      obtain ⟨k, hk, hke⟩ := hk
      have hk1 : k = .var 1 := swapNameAt_injective (by rw [hke]; rfl)
      subst hk1
      rw [Finmap.mem_insert] at hk
      rcases hk with hk | hk
      · simp only [PiCalculus.Name.var.injEq, Nat.one_ne_zero] at hk
      · exact absurd (var_one_mem_lift hk) hxX
    · have h0Y : PiCalculus.Name.var 0 ∈ Y := by
        have h0 : PiCalculus.Name.var 0 ∈ X ∪ Y := by
          rw [← hC]
          exact Finmap.mem_insert.mpr (Or.inl rfl)
        rcases Finmap.mem_union.mp h0 with h0 | h0
        · exact absurd h0 hxX
        · exact h0
      obtain ⟨Y', X', hC', hr'', hq'', hYX', h0X'⟩ := rebalance_cut
        (hC.trans (Finmap.union_comm_of_disjoint hXY)) (Finmap.Disjoint.symm _ _ hXY) h0Y hr' hq'
        (var_not_mem_freeNames_liftAt r 1) (by rw [Proc.absorbs_rename]; exact hx)
      exact ⟨X', Y', hC'.trans (Finmap.union_comm_of_disjoint hYX'), hq'', hr'',
        Finmap.Disjoint.symm _ _ hYX', h0X'⟩
  have hq₀ : HasType (Context.mapKeys (PiCalculus.swapNameAt 0) swapNameAt_injective
      (X.lift.insert (PiCalculus.Name.var 0) b)) q := by
    have hs := HasType.swap hq'
    rwa [Proc.rename_comp, show PiCalculus.swapNameAt 0 ∘ PiCalculus.swapNameAt 0 = id from
      funext swapNameAt_involutive, Proc.rename_id] at hs
  rw [Finmap.union_comm_of_disjoint hXY] at hC
  obtain ⟨Y₀, X₀, rfl, rfl, rfl, hYX⟩ :=
    split_cut_context hC (Finmap.Disjoint.symm _ _ hXY) hxX
  rw [Finmap.disjoint_union_right] at hPD
  have hr₀ : HasType (Y₀.lift.insert (.var 0) b.dual) r :=
    HasType.lowering 1 (by rw [mapKeys_insert, ← lift_lift]; exact hr')
  have hq₁ : HasType
      ((Context.lift (X₀.lift.insert (PiCalculus.Name.var 0) b)).insert (.var 0) a.dual) q := by
    rw [lift_insert, mapKeys_insert, mapKeys_insert, mapKeys_swap_lift_lift] at hq₀
    rw [lift_insert]
    convert hq₀ using 1
    exact insert_insert_comm (by decide)
  have hp₁ : HasType (P₀.lift.lift.insert (.var 0) a) (p.liftAt 1) := by
    have hl1 := HasType.liftAt hp 1
    rw [mapKeys_insert, ← lift_lift] at hl1
    exact hl1
  have hPX : Finmap.Disjoint P₀.lift (X₀.lift.insert (.var 0) b) := by
    intro k hk hkX
    rw [Finmap.mem_insert] at hkX
    rcases hkX with rfl | hkX
    · exact var_zero_not_mem_lift P₀ hk
    · exact disjoint_lift hPD.2 k hk hkX
  have hin := HasType.cut hp₁ hq₁ hPX
  rw [union_insert_right (var_zero_not_mem_lift P₀), ← lift_union hPD.2] at hin
  have hPXY : Finmap.Disjoint (P₀ ∪ X₀) Y₀ :=
    (Finmap.disjoint_union_left _ _ _).mpr ⟨hPD.1, Finmap.Disjoint.symm _ _ hYX⟩
  rw [Finmap.union_comm_of_disjoint hYX, ← Finmap.union_assoc]
  exact HasType.cut hin hr₀ hPXY

/-- Structural equivalence preserves cut shape in both directions. -/
private theorem Cong.isCut_iff {p q : Proc Atom} (h : Cong p q) :
    (∃ a p₁ p₂, p = .cut a p₁ p₂) ↔ (∃ a q₁ q₂, q = .cut a q₁ q₂) := by
  induction h with
  | refl => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap a p q => exact ⟨fun _ => ⟨_, _, _, rfl⟩, fun _ => ⟨_, _, _, rfl⟩⟩
  | assoc a b p q r _ _ => exact ⟨fun _ => ⟨_, _, _, rfl⟩, fun _ => ⟨_, _, _, rfl⟩⟩

/-- Structural equivalence preserves typing in both directions. -/
theorem Cong.hasType_iff {Γ : Context Atom} {p q : Proc Atom}
    (h : Cong p q) : HasType Γ p ↔ HasType Γ q := by
  induction h generalizing Γ with
  | refl => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap a p q =>
    refine ⟨HasType.cut_swap, fun h => ?_⟩
    have hs := h.cut_swap
    rwa [Logic.CLL.Proposition.dual_involution] at hs
  | assoc a b p q r hy hx => exact ⟨HasType.assoc_fwd hy, HasType.assoc_bwd hx⟩

/-- Associativity in the source's derivation shape: when the middle
component of a left-nested cut is typed with both cut channels in its
environment, the cut reassociates. -/
theorem Cong.assoc_of_hasType {Γ : Context Atom} {a b : Logic.CLL.Proposition Atom}
    {p q r : Proc Atom}
    (hq : HasType ((Context.lift (Γ.lift.insert (.var 0) b)).insert (.var 0) a.dual) q) :
    Cong (.cut b (.cut a (p.liftAt 1) q) r)
      (.cut a p (.cut b (q.rename (PiCalculus.swapNameAt 0)) (r.liftAt 1))) := by
  have hown : ∀ k, k ∈ (Context.lift (Γ.lift.insert (.var 0) b)).insert (.var 0) a.dual →
      k ∈ q.freeNames ∨ q.absorbs = true := fun k hk => by
    by_cases hf : k ∈ q.freeNames
    · exact Or.inl hf
    · exact Or.inr (hq.absorbs_of_unused hk hf)
  refine Cong.assoc a b p q r (hown (.var 1) ?_)
    (hown (.var 0) (Finmap.mem_insert.mpr (Or.inl rfl)))
  exact Finmap.mem_insert.mpr
    (Or.inr (mem_lift.mpr ⟨.var 0, Finmap.mem_insert.mpr (Or.inl rfl), rfl⟩))

/-! ## Reduction -/

/-- One-step reduction of classical processes: principal cut reductions,
commuting conversions, reduction under a cut, and closure under
structural equivalence. The rule `axCutSymm`, the link-symmetric
orientation of axiom cut, is an extension beyond the printed figure,
included because cut symmetry alone does not produce that redex. The
`commTensorLeft` and `commTensorRight` rules require the cut channel to
be free in, or absorbable by, the component that receives the cut:
Figure 4's `fn` side conditions extended to channels owned through `⊤`. -/
inductive Step : Proc Atom → Proc Atom → Prop where
  | axCut (a : Logic.CLL.Proposition Atom) (w : PiCalculus.Name)
      (p : Proc Atom) :
      Step (.cut a (.link (PiCalculus.liftName 0 w) (.var 0)) p)
        (p.subst w)
  | axCutSymm (a : Logic.CLL.Proposition Atom) (w : PiCalculus.Name)
      (p : Proc Atom) :
      Step (.cut a (.link (.var 0) (PiCalculus.liftName 0 w)) p)
        (p.subst w)
  | tensorParr (a b : Logic.CLL.Proposition Atom) (p q r : Proc Atom) :
      Step (.cut (.tensor a b) (.output (.var 0) p q) (.input (.var 0) r))
        (.cut b q (.cut a p r))
  | oplusWithLeft (a b : Logic.CLL.Proposition Atom) (p q r : Proc Atom) :
      Step (.cut (.oplus a b) (.selectLeft (.var 0) p)
          (.choice (.var 0) q r))
        (.cut a p q)
  | oplusWithRight (a b : Logic.CLL.Proposition Atom) (p q r : Proc Atom) :
      Step (.cut (.oplus a b) (.selectRight (.var 0) p)
          (.choice (.var 0) q r))
        (.cut b p r)
  | oneBot (p : Proc Atom) :
      Step (.cut .one (.emptyOutput (.var 0)) (.emptyInput (.var 0) (p.liftAt 0))) p
  | commTensorLeft (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q r : Proc Atom) (hz : PiCalculus.Name.var 1 ∈ p.freeNames ∨ p.absorbs = true) :
      Step (.cut c (.output (PiCalculus.liftName 0 x) p (q.liftAt 0)) r)
        (.output x (.cut c (p.rename (PiCalculus.swapNameAt 0))
          (r.liftAt 1)) q)
  | commTensorRight (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q r : Proc Atom) (hz : PiCalculus.Name.var 0 ∈ q.freeNames ∨ q.absorbs = true) :
      Step (.cut c (.output (PiCalculus.liftName 0 x) (p.liftAt 1) q) r)
        (.output x p (.cut c q r))
  | commParr (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q : Proc Atom) :
      Step (.cut c (.input (PiCalculus.liftName 0 x) p) q)
        (.input x (.cut c (p.rename (PiCalculus.swapNameAt 0)) (q.liftAt 1)))
  | commSelectLeft (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q : Proc Atom) :
      Step (.cut c (.selectLeft (PiCalculus.liftName 0 x) p) q)
        (.selectLeft x (.cut c p q))
  | commSelectRight (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q : Proc Atom) :
      Step (.cut c (.selectRight (PiCalculus.liftName 0 x) p) q)
        (.selectRight x (.cut c p q))
  | commChoice (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q r : Proc Atom) :
      Step (.cut c (.choice (PiCalculus.liftName 0 x) p q) r)
        (.choice x (.cut c p r) (.cut c q r))
  | commBot (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (p q : Proc Atom) :
      Step (.cut c (.emptyInput (PiCalculus.liftName 0 x) p) q)
        (.emptyInput x (.cut c p q))
  | commTop (c : Logic.CLL.Proposition Atom) (x : PiCalculus.Name)
      (q : Proc Atom) :
      Step (.cut c (.emptyChoice (PiCalculus.liftName 0 x)) q)
        (.emptyChoice x)
  | cutLeft (a : Logic.CLL.Proposition Atom) {p p' : Proc Atom}
      (h : Step p p') (q : Proc Atom) :
      Step (.cut a p q) (.cut a p' q)
  | cutRight (a : Logic.CLL.Proposition Atom) (p : Proc Atom)
      {q q' : Proc Atom} (h : Step q q') :
      Step (.cut a p q) (.cut a p q')
  | cong {p p' q' q : Proc Atom} (h₁ : Cong p p') (h₂ : Step p' q')
      (h₃ : Cong q' q) :
      Step p q

/-- Multi-step reduction: the reflexive-transitive closure of `Step`. -/
def Steps : Proc Atom → Proc Atom → Prop :=
  Relation.ReflTransGen Step

/-- Inversion of the axiom rule. -/
private theorem HasType.link_inv {C : Context Atom} {w x : PiCalculus.Name}
    (h : HasType C (.link w x)) :
    ∃ a : Logic.CLL.Proposition Atom, w ≠ x ∧
      C = ((∅ : Context Atom).insert w a.dual).insert x a := by
  cases h with
  | ax hwx => exact ⟨_, hwx, rfl⟩

/-- Inversion of the `1` rule. -/
private theorem HasType.emptyOutput_inv {C : Context Atom} {x : PiCalculus.Name}
    (h : HasType C (.emptyOutput x)) : C = (∅ : Context Atom).insert x .one := by
  cases h
  rfl

/-- Inversion of the `⊗` rule. -/
private theorem HasType.output_inv {C : Context Atom} {x : PiCalculus.Name}
    {p q : Proc Atom} (h : HasType C (.output x p q)) :
    ∃ (Γ Δ : Context Atom) (a b : Logic.CLL.Proposition Atom),
      C = (Γ ∪ Δ).insert x (.tensor a b) ∧ HasType (Γ.lift.insert (.var 0) a) p ∧
      HasType (Δ.insert x b) q ∧ Finmap.Disjoint Γ Δ ∧ x ∉ Γ ∧ x ∉ Δ := by
  cases h with
  | tensor hp hq hd hxΓ hxΔ => exact ⟨_, _, _, _, rfl, hp, hq, hd, hxΓ, hxΔ⟩

/-- Inversion of the `⅋` rule. -/
private theorem HasType.input_inv {C : Context Atom} {x : PiCalculus.Name}
    {p : Proc Atom} (h : HasType C (.input x p)) :
    ∃ (Γ : Context Atom) (a b : Logic.CLL.Proposition Atom),
      C = Γ.insert x (.parr a b) ∧
      HasType ((Γ.lift.insert (.var 0) a).insert (PiCalculus.liftName 0 x) b) p ∧
      x ∉ Γ := by
  cases h with
  | parr hp hxΓ => exact ⟨_, _, _, rfl, hp, hxΓ⟩

/-- Inversion of the left `⊕` rule. -/
private theorem HasType.selectLeft_inv {C : Context Atom} {x : PiCalculus.Name}
    {p : Proc Atom} (h : HasType C (.selectLeft x p)) :
    ∃ (Γ : Context Atom) (a b : Logic.CLL.Proposition Atom),
      C = Γ.insert x (.oplus a b) ∧ HasType (Γ.insert x a) p ∧ x ∉ Γ := by
  cases h with
  | oplusLeft hp hxΓ => exact ⟨_, _, _, rfl, hp, hxΓ⟩

/-- Inversion of the right `⊕` rule. -/
private theorem HasType.selectRight_inv {C : Context Atom} {x : PiCalculus.Name}
    {p : Proc Atom} (h : HasType C (.selectRight x p)) :
    ∃ (Γ : Context Atom) (a b : Logic.CLL.Proposition Atom),
      C = Γ.insert x (.oplus a b) ∧ HasType (Γ.insert x b) p ∧ x ∉ Γ := by
  cases h with
  | oplusRight hp hxΓ => exact ⟨_, _, _, rfl, hp, hxΓ⟩

/-- Inversion of the `&` rule. -/
private theorem HasType.choice_inv {C : Context Atom} {x : PiCalculus.Name}
    {p q : Proc Atom} (h : HasType C (.choice x p q)) :
    ∃ (Γ : Context Atom) (a b : Logic.CLL.Proposition Atom),
      C = Γ.insert x (.with a b) ∧ HasType (Γ.insert x a) p ∧
      HasType (Γ.insert x b) q ∧ x ∉ Γ := by
  cases h with
  | «with» hp hq hxΓ => exact ⟨_, _, _, rfl, hp, hq, hxΓ⟩

/-- Inversion of the `⊥` rule. -/
private theorem HasType.emptyInput_inv {C : Context Atom} {x : PiCalculus.Name}
    {p : Proc Atom} (h : HasType C (.emptyInput x p)) :
    ∃ Γ : Context Atom, C = Γ.insert x .bot ∧ HasType Γ p ∧ x ∉ Γ := by
  cases h with
  | bot hp hxΓ => exact ⟨_, rfl, hp, hxΓ⟩

/-- Inversion of the `⊤` rule. -/
private theorem HasType.emptyChoice_inv {C : Context Atom} {x : PiCalculus.Name}
    (h : HasType C (.emptyChoice x)) :
    ∃ Γ : Context Atom, C = Γ.insert x .top ∧ x ∉ Γ := by
  cases h with
  | top hxΓ => exact ⟨_, rfl, hxΓ⟩

/-- Preservation for the axiom cut. -/
private theorem HasType.step_axCut {Γ : Context Atom} {a : Logic.CLL.Proposition Atom}
    {w : PiCalculus.Name} {p : Proc Atom}
    (h : HasType Γ (.cut a (.link (PiCalculus.liftName 0 w) (.var 0)) p)) :
    HasType Γ (p.subst w) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨a', hne, he⟩ := hl.link_inv
  have hv : PiCalculus.Name.var 0 ∉
      (∅ : Context Atom).insert (PiCalculus.liftName 0 w) a'.dual := by
    rw [Finmap.mem_insert]
    rintro (h | h)
    · exact hne h.symm
    · exact Finmap.notMem_empty h
  obtain ⟨hG, rfl⟩ := insert_cancel (var_zero_not_mem_lift G) hv he
  have hG' : G = (∅ : Context Atom).insert w a.dual :=
    mapKeys_injective (liftName_injective 0) (by
      change G.lift = Context.lift _
      rw [hG, lift_insert]
      rfl)
  subst hG'
  have hw : w ∉ R := fun hw => hd w (Finmap.mem_insert.mpr (Or.inl rfl)) hw
  rw [insert_union_comm (Finmap.disjoint_empty R) hw, Finmap.empty_union]
  exact HasType.subst hr hw

/-- Preservation for the symmetric axiom cut. -/
private theorem HasType.step_axCutSymm {Γ : Context Atom} {a : Logic.CLL.Proposition Atom}
    {w : PiCalculus.Name} {p : Proc Atom}
    (h : HasType Γ (.cut a (.link (.var 0) (PiCalculus.liftName 0 w)) p)) :
    HasType Γ (p.subst w) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨a', hne, he⟩ := hl.link_inv
  rw [insert_insert_comm hne] at he
  have hv : PiCalculus.Name.var 0 ∉
      (∅ : Context Atom).insert (PiCalculus.liftName 0 w) a' := by
    rw [Finmap.mem_insert]
    rintro (h | h)
    · exact hne h
    · exact Finmap.notMem_empty h
  obtain ⟨hG, rfl⟩ := insert_cancel (var_zero_not_mem_lift G) hv he
  have hG' : G = (∅ : Context Atom).insert w a' :=
    mapKeys_injective (liftName_injective 0) (by
      change G.lift = Context.lift _
      rw [hG, lift_insert]
      rfl)
  subst hG'
  have hw : w ∉ R := fun hw => hd w (Finmap.mem_insert.mpr (Or.inl rfl)) hw
  rw [insert_union_comm (Finmap.disjoint_empty R) hw, Finmap.empty_union]
  rw [Logic.CLL.Proposition.dual_involution] at hr
  exact HasType.subst hr hw

/-- Preservation for the principal tensor/par cut. -/
private theorem HasType.step_tensorParr {Γ : Context Atom}
    {a b : Logic.CLL.Proposition Atom} {p q r : Proc Atom}
    (h : HasType Γ (.cut (.tensor a b) (.output (.var 0) p q) (.input (.var 0) r))) :
    HasType Γ (.cut b q (.cut a p r)) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, Y, a', b', he, hp, hq, hXY, hxX, hxY⟩ := hl.output_inv
  have hv : PiCalculus.Name.var 0 ∉ X ∪ Y := by
    rw [Finmap.mem_union]
    rintro (h | h)
    · exact hxX h
    · exact hxY h
  obtain ⟨hG, hab⟩ := insert_cancel (var_zero_not_mem_lift G) hv he
  obtain ⟨rfl, rfl⟩ := Logic.CLL.Proposition.tensor.inj hab
  obtain ⟨X₀, rfl⟩ := exists_unlift hxX
  obtain ⟨Y₀, rfl⟩ := exists_unlift hxY
  have hXY₀ : Finmap.Disjoint X₀ Y₀ := fun x hx hy =>
    hXY _ (mem_lift.mpr ⟨x, hx, rfl⟩) (mem_lift.mpr ⟨x, hy, rfl⟩)
  have hG₀ : G = X₀ ∪ Y₀ := mapKeys_injective (liftName_injective 0) (by
    change G.lift = (X₀ ∪ Y₀).lift
    rw [lift_union hXY₀]
    exact hG)
  subst hG₀
  obtain ⟨Z, a'', b'', he', hr', hz⟩ := hr.input_inv
  obtain ⟨hR, hab'⟩ := insert_cancel (var_zero_not_mem_lift R) hz he'
  obtain ⟨rfl, rfl⟩ := Logic.CLL.Proposition.parr.inj hab'
  subst hR
  rw [Finmap.disjoint_union_left] at hd
  have hr₂ : HasType
      ((Context.lift (R.lift.insert (PiCalculus.Name.var 0) b.dual)).insert (.var 0) a.dual) r := by
    rw [lift_insert]
    convert hr' using 1
    exact insert_insert_comm (by decide)
  have hXR : Finmap.Disjoint X₀.lift (R.lift.insert (.var 0) b.dual) := by
    intro k hk hkR
    rw [Finmap.mem_insert] at hkR
    rcases hkR with rfl | hkR
    · exact var_zero_not_mem_lift X₀ hk
    · exact disjoint_lift hd.1 k hk hkR
  have hin := HasType.cut hp hr₂ hXR
  rw [union_insert_right (var_zero_not_mem_lift X₀), ← lift_union hd.1] at hin
  have hdisj : Finmap.Disjoint Y₀ (X₀ ∪ R) :=
    (Finmap.disjoint_union_right _ _ _).mpr ⟨Finmap.Disjoint.symm _ _ hXY₀, hd.2⟩
  rw [Finmap.union_comm_of_disjoint hXY₀, Finmap.union_assoc]
  exact HasType.cut hq hin hdisj

/-- Preservation for the principal left `⊕`/`&` cut. -/
private theorem HasType.step_oplusWithLeft {Γ : Context Atom}
    {a b : Logic.CLL.Proposition Atom} {p q r : Proc Atom}
    (h : HasType Γ (.cut (.oplus a b) (.selectLeft (.var 0) p) (.choice (.var 0) q r))) :
    HasType Γ (.cut a p q) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, a', b', he, hp, hx⟩ := hl.selectLeft_inv
  obtain ⟨hG, hab⟩ := insert_cancel (var_zero_not_mem_lift G) hx he
  obtain ⟨rfl, rfl⟩ := Logic.CLL.Proposition.oplus.inj hab
  subst hG
  obtain ⟨Y, a'', b'', he', hq, _, hy⟩ := hr.choice_inv
  obtain ⟨hR, hab'⟩ := insert_cancel (var_zero_not_mem_lift R) hy he'
  obtain ⟨rfl, rfl⟩ := Logic.CLL.Proposition.with.inj hab'
  subst hR
  exact HasType.cut hp hq hd

/-- Preservation for the principal right `⊕`/`&` cut. -/
private theorem HasType.step_oplusWithRight {Γ : Context Atom}
    {a b : Logic.CLL.Proposition Atom} {p q r : Proc Atom}
    (h : HasType Γ (.cut (.oplus a b) (.selectRight (.var 0) p) (.choice (.var 0) q r))) :
    HasType Γ (.cut b p r) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, a', b', he, hp, hx⟩ := hl.selectRight_inv
  obtain ⟨hG, hab⟩ := insert_cancel (var_zero_not_mem_lift G) hx he
  obtain ⟨rfl, rfl⟩ := Logic.CLL.Proposition.oplus.inj hab
  subst hG
  obtain ⟨Y, a'', b'', he', _, hr', hy⟩ := hr.choice_inv
  obtain ⟨hR, hab'⟩ := insert_cancel (var_zero_not_mem_lift R) hy he'
  obtain ⟨rfl, rfl⟩ := Logic.CLL.Proposition.with.inj hab'
  subst hR
  exact HasType.cut hp hr' hd

/-- Preservation for the principal `1`/`⊥` cut. -/
private theorem HasType.step_oneBot {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ (.cut .one (.emptyOutput (.var 0)) (.emptyInput (.var 0) (p.liftAt 0)))) :
    HasType Γ p := by
  obtain ⟨G, R, rfl, hl, hr, _⟩ := h.cut_inv
  obtain ⟨hG, -⟩ := insert_cancel (var_zero_not_mem_lift G) Finmap.notMem_empty hl.emptyOutput_inv
  have hG' : G = ∅ := mapKeys_injective (liftName_injective 0) (by
    change G.lift = Context.lift ∅
    rw [hG]
    rfl)
  subst hG'
  obtain ⟨Y, he, hb, hy⟩ := hr.emptyInput_inv
  obtain ⟨hR, -⟩ := insert_cancel (var_zero_not_mem_lift R) hy he
  subst hR
  rw [Finmap.empty_union]
  exact HasType.lowering 0 hb

/-- Key ownership for a commuting conversion: when the left premise of a
cut acts on a free channel `liftName 0 x`, the cut's left environment
owns `x`, and the action's remaining environment is the lowered rest with
the cut channel. -/
private theorem peel_cut_context {G Δ : Context Atom} {c v : Logic.CLL.Proposition Atom}
    {x : PiCalculus.Name} (hx : PiCalculus.liftName 0 x ∉ Δ)
    (h : G.lift.insert (.var 0) c = Δ.insert (PiCalculus.liftName 0 x) v) :
    ∃ G₁ : Context Atom, G = G₁.insert x v ∧ x ∉ G₁ ∧
      Δ = G₁.lift.insert (.var 0) c := by
  have hne := liftName_zero_ne_var_zero x
  have hlk : G.lookup x = some v := by
    have hl := congrArg (Finmap.lookup (PiCalculus.liftName 0 x)) h
    rw [Finmap.lookup_insert_of_ne _ hne, Finmap.lookup_insert] at hl
    rw [← hl]
    exact (lookup_mapKeys_apply _ G x).symm
  have hG : G = (G.erase x).insert x v := by
    apply Finmap.ext_lookup
    intro y
    by_cases hy : y = x
    · subst hy
      rw [hlk, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hy, Finmap.lookup_erase_ne hy]
  have hxE : x ∉ G.erase x := fun hm => (Finmap.mem_erase.mp hm).1 rfl
  refine ⟨G.erase x, hG, hxE, ?_⟩
  rw [hG, lift_insert, insert_insert_comm hne] at h
  have hx₁ : PiCalculus.liftName 0 x ∉ (Context.lift (G.erase x)).insert (.var 0) c := by
    rw [Finmap.mem_insert]
    rintro (hm | hm)
    · exact hne hm
    · obtain ⟨y, hy, he⟩ := mem_lift.mp hm
      rw [liftName_injective 0 he] at hy
      exact hxE hy
  exact (insert_cancel hx₁ hx h).1.symm

/-- Splitting a disjointness hypothesis whose left side is an insertion. -/
private theorem disjoint_insert_left {G R : Context Atom} {x : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (h : Finmap.Disjoint (G.insert x v) R) :
    x ∉ R ∧ Finmap.Disjoint G R :=
  ⟨fun hx => h x (Finmap.mem_insert.mpr (Or.inl rfl)) hx,
    fun k hk hkR => h k (Finmap.mem_insert.mpr (Or.inr hk)) hkR⟩

/-- Building a disjointness hypothesis whose left side is an insertion. -/
private theorem disjoint_insert_of {G R : Context Atom} {x : PiCalculus.Name}
    {v : Logic.CLL.Proposition Atom} (hx : x ∉ R) (h : Finmap.Disjoint G R) :
    Finmap.Disjoint (G.insert x v) R := by
  intro k hk hkR
  rw [Finmap.mem_insert] at hk
  rcases hk with rfl | hk
  · exact hx hkR
  · exact h k hk hkR

/-- Disjointness of an insertion at `var 0` into a lift from a lift. -/
private theorem disjoint_insert_var_zero_lift {A R : Context Atom}
    {v : Logic.CLL.Proposition Atom} (h : Finmap.Disjoint A R) :
    Finmap.Disjoint (A.lift.insert (.var 0) v) R.lift :=
  disjoint_insert_of (var_zero_not_mem_lift R) (disjoint_lift h)

/-- Preservation for the left tensor commuting conversion. -/
private theorem HasType.step_commTensorLeft {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q r : Proc Atom}
    (hz : PiCalculus.Name.var 1 ∈ p.freeNames ∨ p.absorbs = true)
    (h : HasType Γ (.cut c (.output (PiCalculus.liftName 0 x) p (q.liftAt 0)) r)) :
    HasType Γ (.output x (.cut c (p.rename (PiCalculus.swapNameAt 0)) (r.liftAt 1)) q) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, Y, a, b, he, hp, hq, hXY, hxX, hxY, hzX⟩ :
      ∃ (X Y : Context Atom) (a b : Logic.CLL.Proposition Atom),
        G.lift.insert (.var 0) c =
            (X ∪ Y).insert (PiCalculus.liftName 0 x) (.tensor a b) ∧
          HasType (X.lift.insert (.var 0) a) p ∧
          HasType (Y.insert (PiCalculus.liftName 0 x) b) (q.liftAt 0) ∧
          Finmap.Disjoint X Y ∧ PiCalculus.liftName 0 x ∉ X ∧ PiCalculus.liftName 0 x ∉ Y ∧
          PiCalculus.Name.var 0 ∈ X := by
    obtain ⟨X, Y, a, b, he, hp, hq, hXY, hxX, hxY⟩ := hl.output_inv
    by_cases hzX : PiCalculus.Name.var 0 ∈ X
    · exact ⟨X, Y, a, b, he, hp, hq, hXY, hxX, hxY, hzX⟩
    rcases hz with hz | hz
    · have hk := HasType.freeNames_subset_keys hp hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hk
      rcases hk with hk | hk
      · simp only [PiCalculus.Name.var.injEq, Nat.one_ne_zero] at hk
      · exact absurd (var_one_mem_lift hk) hzX
    · have hzY : PiCalculus.Name.var 0 ∈ Y := by
        have h0 : PiCalculus.Name.var 0 ∈
            (X ∪ Y).insert (PiCalculus.liftName 0 x) (.tensor a b) := by
          rw [← he]
          exact Finmap.mem_insert.mpr (Or.inl rfl)
        rw [Finmap.mem_insert, Finmap.mem_union] at h0
        rcases h0 with h0 | h0 | h0
        · exact absurd h0.symm (liftName_zero_ne_var_zero x)
        · exact absurd h0 hzX
        · exact h0
      have hlk : Y.lookup (.var 0) = some c := by
        have e := congrArg (Finmap.lookup (PiCalculus.Name.var 0)) he
        rw [Finmap.lookup_insert,
          Finmap.lookup_insert_of_ne _ (Ne.symm (liftName_zero_ne_var_zero x)),
          Finmap.lookup_union_right hzX] at e
        exact e.symm
      have hq' := hq.strengthen (var_not_mem_freeNames_liftAt q 0)
      rw [erase_insert_of_ne (Ne.symm (liftName_zero_ne_var_zero x))] at hq'
      have hp' := hp.weaken_absorbs hz (k := .var 1) (v := c) (by
        rw [Finmap.mem_insert, not_or]
        exact ⟨by decide, fun h => hzX (var_one_mem_lift h)⟩)
      rw [insert_insert_comm (by decide),
        show (PiCalculus.Name.var 1) = PiCalculus.liftName 0 (.var 0) from rfl,
        ← lift_insert] at hp'
      refine ⟨X.insert (.var 0) c, Y.erase (.var 0), a, b, ?_, hp', hq', ?_, ?_, ?_,
        Finmap.mem_insert.mpr (Or.inl rfl)⟩
      · rw [he, union_move_left hzY hlk hzX]
      · exact Finmap.Disjoint.symm _ _ (disjoint_erase_insert (Finmap.Disjoint.symm _ _ hXY))
      · rw [Finmap.mem_insert, not_or]
        exact ⟨liftName_zero_ne_var_zero x, hxX⟩
      · exact fun h => hxY (Finmap.mem_erase.mp h).2
  have hxXY : PiCalculus.liftName 0 x ∉ X ∪ Y := by
    rw [Finmap.mem_union]
    rintro (hm | hm)
    · exact hxX hm
    · exact hxY hm
  obtain ⟨G₁, rfl, hxG₁, hE⟩ := peel_cut_context hxXY he
  rw [Finmap.union_comm_of_disjoint hXY] at hE
  obtain ⟨Y₀, X₀, rfl, rfl, rfl, hYX⟩ :=
    split_cut_context hE.symm (Finmap.Disjoint.symm _ _ hXY) hzX
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hdR' := hdR
  rw [Finmap.disjoint_union_left] at hdR'
  rw [Finmap.mem_union, not_or] at hxG₁
  have hq' : HasType (Y₀.insert x b) q :=
    HasType.lowering 0 (by rw [mapKeys_insert]; exact hq)
  have hp' : HasType ((Context.lift (X₀.lift.insert (PiCalculus.Name.var 0) a)).insert
      (.var 0) c) (p.rename (PiCalculus.swapNameAt 0)) := by
    have hs := HasType.swap hp
    rw [lift_insert, mapKeys_insert, mapKeys_insert, mapKeys_swap_lift_lift] at hs
    rw [lift_insert]
    convert hs using 1
    exact insert_insert_comm (by decide)
  have hr' : HasType (R.lift.lift.insert (.var 0) c.dual) (r.liftAt 1) := by
    have hl1 := HasType.liftAt hr 1
    rw [mapKeys_insert, ← lift_lift] at hl1
    exact hl1
  have hin := HasType.cut hp' hr' (disjoint_insert_var_zero_lift hdR'.2)
  rw [insert_union_comm (disjoint_lift hdR'.2) (var_zero_not_mem_lift R),
    ← lift_union hdR'.2] at hin
  have hdisj : Finmap.Disjoint (X₀ ∪ R) Y₀ :=
    (Finmap.disjoint_union_left _ _ _).mpr
      ⟨Finmap.Disjoint.symm _ _ hYX, Finmap.Disjoint.symm _ _ hdR'.1⟩
  have hout := HasType.tensor hin hq' hdisj
    (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁.2, hxR⟩) hxG₁.1
  rw [insert_union_comm hdR hxR, Finmap.union_comm_of_disjoint hYX, Finmap.union_assoc,
    Finmap.union_comm_of_disjoint hdR'.1, ← Finmap.union_assoc]
  exact hout

/-- Preservation for the right tensor commuting conversion. -/
private theorem HasType.step_commTensorRight {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q r : Proc Atom}
    (hz : PiCalculus.Name.var 0 ∈ q.freeNames ∨ q.absorbs = true)
    (h : HasType Γ (.cut c (.output (PiCalculus.liftName 0 x) (p.liftAt 1) q) r)) :
    HasType Γ (.output x p (.cut c q r)) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, Y, a, b, he, hp, hq, hXY, hxX, hxY, hzY⟩ :
      ∃ (X Y : Context Atom) (a b : Logic.CLL.Proposition Atom),
        G.lift.insert (.var 0) c =
            (X ∪ Y).insert (PiCalculus.liftName 0 x) (.tensor a b) ∧
          HasType (X.lift.insert (.var 0) a) (p.liftAt 1) ∧
          HasType (Y.insert (PiCalculus.liftName 0 x) b) q ∧
          Finmap.Disjoint X Y ∧ PiCalculus.liftName 0 x ∉ X ∧ PiCalculus.liftName 0 x ∉ Y ∧
          PiCalculus.Name.var 0 ∈ Y := by
    obtain ⟨X, Y, a, b, he, hp, hq, hXY, hxX, hxY⟩ := hl.output_inv
    by_cases hzY : PiCalculus.Name.var 0 ∈ Y
    · exact ⟨X, Y, a, b, he, hp, hq, hXY, hxX, hxY, hzY⟩
    rcases hz with hz | hz
    · have hk := HasType.freeNames_subset_keys hq hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hk
      rcases hk with hk | hk
      · exact absurd hk.symm (liftName_zero_ne_var_zero x)
      · exact absurd hk hzY
    · have hzX : PiCalculus.Name.var 0 ∈ X := by
        have h0 : PiCalculus.Name.var 0 ∈
            (X ∪ Y).insert (PiCalculus.liftName 0 x) (.tensor a b) := by
          rw [← he]
          exact Finmap.mem_insert.mpr (Or.inl rfl)
        rw [Finmap.mem_insert, Finmap.mem_union] at h0
        rcases h0 with h0 | h0 | h0
        · exact absurd h0.symm (liftName_zero_ne_var_zero x)
        · exact h0
        · exact absurd h0 hzY
      have hlk : X.lookup (.var 0) = some c := by
        have e := congrArg (Finmap.lookup (PiCalculus.Name.var 0)) he
        rw [Finmap.lookup_insert,
          Finmap.lookup_insert_of_ne _ (Ne.symm (liftName_zero_ne_var_zero x)),
          Finmap.lookup_union_left hzX] at e
        exact e.symm
      have hp' := hp.strengthen (var_not_mem_freeNames_liftAt p 1)
      rw [erase_insert_of_ne (by decide),
        show (PiCalculus.Name.var 1) = PiCalculus.liftName 0 (.var 0) from rfl,
        ← lift_erase] at hp'
      have hq' := hq.weaken_absorbs hz (k := .var 0) (v := c) (by
        rw [Finmap.mem_insert, not_or]
        exact ⟨Ne.symm (liftName_zero_ne_var_zero x), hzY⟩)
      rw [insert_insert_comm (liftName_zero_ne_var_zero x)] at hq'
      refine ⟨X.erase (.var 0), Y.insert (.var 0) c, a, b, ?_, hp', hq',
        disjoint_erase_insert hXY, ?_, ?_, Finmap.mem_insert.mpr (Or.inl rfl)⟩
      · rw [he, union_move_right hzX hlk]
      · exact fun h => hxX (Finmap.mem_erase.mp h).2
      · rw [Finmap.mem_insert, not_or]
        exact ⟨liftName_zero_ne_var_zero x, hxY⟩
  have hxXY : PiCalculus.liftName 0 x ∉ X ∪ Y := by
    rw [Finmap.mem_union]
    rintro (hm | hm)
    · exact hxX hm
    · exact hxY hm
  obtain ⟨G₁, rfl, hxG₁, hE⟩ := peel_cut_context hxXY he
  obtain ⟨X₀, Y₀, rfl, rfl, rfl, hXY₀⟩ := split_cut_context hE.symm hXY hzY
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hdR' := hdR
  rw [Finmap.disjoint_union_left] at hdR'
  rw [Finmap.mem_union, not_or] at hxG₁
  have hp' : HasType (X₀.lift.insert (.var 0) a) p :=
    HasType.lowering 1 (by rw [mapKeys_insert, ← lift_lift]; exact hp)
  have hq' : HasType ((Context.lift (Y₀.insert x b)).insert (.var 0) c) q := by
    rw [lift_insert, insert_insert_comm (liftName_zero_ne_var_zero x)]
    exact hq
  have hin := HasType.cut hq' hr (disjoint_insert_of hxR hdR'.2)
  rw [insert_union_comm hdR'.2 hxR] at hin
  have hdisj : Finmap.Disjoint X₀ (Y₀ ∪ R) :=
    (Finmap.disjoint_union_right _ _ _).mpr ⟨hXY₀, hdR'.1⟩
  have hout := HasType.tensor hp' hin hdisj hxG₁.1
    (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁.2, hxR⟩)
  rw [insert_union_comm hdR hxR, Finmap.union_assoc]
  exact hout

/-- A typed cut against an output on another channel always takes a
tensor commuting step, whichever output component the derivation gives
the cut channel to. -/
theorem Step.commTensor_of_hasType {Γ : Context Atom} {c : Logic.CLL.Proposition Atom}
    {x : PiCalculus.Name} {p q r : Proc Atom}
    (h : HasType Γ (.cut c (.output (PiCalculus.liftName 0 x) p q) r)) :
    ∃ s : Proc Atom, Step (.cut c (.output (PiCalculus.liftName 0 x) p q) r) s := by
  obtain ⟨G, R, -, hl, -, -⟩ := h.cut_inv
  obtain ⟨X, Y, a, b, he, hp, hq, hXY, -, -⟩ := hl.output_inv
  have h0 : PiCalculus.Name.var 0 ∈ X ∪ Y := by
    have hm : PiCalculus.Name.var 0 ∈
        (X ∪ Y).insert (PiCalculus.liftName 0 x) (.tensor a b) := by
      rw [← he]
      exact Finmap.mem_insert.mpr (Or.inl rfl)
    rcases Finmap.mem_insert.mp hm with hm | hm
    · exact absurd hm.symm (liftName_zero_ne_var_zero x)
    · exact hm
  rcases Finmap.mem_union.mp h0 with h0 | h0
  · have hq0 : PiCalculus.Name.var 0 ∉ q.freeNames := fun hf => by
      have hk := HasType.freeNames_subset_keys hq hf
      rw [Finmap.mem_keys, Finmap.mem_insert] at hk
      rcases hk with hk | hk
      · exact liftName_zero_ne_var_zero x hk.symm
      · exact hXY _ h0 hk
    obtain ⟨q₀, rfl⟩ := exists_liftAt_of_not_mem q 0 (d := 0) (e := 0) rfl hq0
    have hz : PiCalculus.Name.var 1 ∈ p.freeNames ∨ p.absorbs = true := by
      by_cases hf : PiCalculus.Name.var 1 ∈ p.freeNames
      · exact Or.inl hf
      · exact Or.inr (hp.absorbs_of_unused (k := .var 1)
          (Finmap.mem_insert.mpr (Or.inr (mem_lift.mpr ⟨_, h0, rfl⟩))) hf)
    exact ⟨_, Step.commTensorLeft c x p q₀ r hz⟩
  · have hp1 : PiCalculus.Name.var 1 ∉ p.freeNames := fun hf => by
      have hk := HasType.freeNames_subset_keys hp hf
      rw [Finmap.mem_keys, Finmap.mem_insert] at hk
      rcases hk with hk | hk
      · simp only [PiCalculus.Name.var.injEq, Nat.one_ne_zero] at hk
      · exact hXY _ (var_one_mem_lift hk) h0
    obtain ⟨p₀, rfl⟩ := exists_liftAt_of_not_mem p 1 (d := 0) (e := 1) rfl hp1
    have hz : PiCalculus.Name.var 0 ∈ q.freeNames ∨ q.absorbs = true := by
      by_cases hf : PiCalculus.Name.var 0 ∈ q.freeNames
      · exact Or.inl hf
      · exact Or.inr (hq.absorbs_of_unused (Finmap.mem_insert.mpr (Or.inr h0)) hf)
    exact ⟨_, Step.commTensorRight c x p₀ q r hz⟩

/-- Exchanging the two innermost variables fixes a twice-lifted name. -/
private theorem swapNameAt_liftName_liftName (x : PiCalculus.Name) :
    PiCalculus.swapNameAt 0 (PiCalculus.liftName 0 (PiCalculus.liftName 0 x)) =
      PiCalculus.liftName 0 (PiCalculus.liftName 0 x) := by
  rcases x with n | i
  · rfl
  · simp only [PiCalculus.liftName, PiCalculus.swapNameAt, Nat.zero_le, ↓reduceIte,
      show i + 1 + 1 ≠ 0 by omega, show i + 1 + 1 ≠ 0 + 1 by omega]

/-- Preservation for the par commuting conversion. -/
private theorem HasType.step_commParr {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q : Proc Atom}
    (h : HasType Γ (.cut c (.input (PiCalculus.liftName 0 x) p) q)) :
    HasType Γ (.input x (.cut c (p.rename (PiCalculus.swapNameAt 0)) (q.liftAt 1))) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, a, b, he, hp, hx⟩ := hl.input_inv
  obtain ⟨G₁, rfl, hxG₁, rfl⟩ := peel_cut_context hx he
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hL0 : PiCalculus.Name.var 0 ≠
      PiCalculus.liftName 0 (PiCalculus.liftName 0 x) :=
    (liftName_zero_ne_var_zero _).symm
  have hp' : HasType ((Context.lift ((G₁.lift.insert (PiCalculus.Name.var 0) a).insert
      (PiCalculus.liftName 0 x) b)).insert (.var 0) c) (p.rename (PiCalculus.swapNameAt 0)) := by
    have hs := HasType.swap hp
    rw [lift_insert, mapKeys_insert, mapKeys_insert, mapKeys_insert, mapKeys_swap_lift_lift,
      swapNameAt_liftName_liftName] at hs
    rw [lift_insert, lift_insert]
    simp only [show PiCalculus.liftName 0 (PiCalculus.Name.var 0) = .var 1 from rfl,
      show PiCalculus.swapNameAt 0 (PiCalculus.Name.var 1) = .var 0 from rfl,
      show PiCalculus.swapNameAt 0 (PiCalculus.Name.var 0) = .var 1 from rfl] at hs ⊢
    rw [insert_insert_comm (by decide : PiCalculus.Name.var 0 ≠ .var 1),
      insert_insert_comm hL0] at hs
    exact hs
  have hq' : HasType (R.lift.lift.insert (.var 0) c.dual) (q.liftAt 1) := by
    have hl1 := HasType.liftAt hr 1
    rw [mapKeys_insert, ← lift_lift] at hl1
    exact hl1
  have hxRl : PiCalculus.liftName 0 x ∉ R.lift := by
    intro hm
    obtain ⟨y, hy, he'⟩ := mem_lift.mp hm
    rw [liftName_injective 0 he'] at hy
    exact hxR hy
  have hdl : Finmap.Disjoint
      ((G₁.lift.insert (PiCalculus.Name.var 0) a).insert (PiCalculus.liftName 0 x) b) R.lift :=
    disjoint_insert_of hxRl (disjoint_insert_var_zero_lift hdR)
  have hin := HasType.cut hp' hq' hdl
  rw [insert_union_comm (disjoint_insert_var_zero_lift hdR) hxRl,
    insert_union_comm (disjoint_lift hdR) (var_zero_not_mem_lift R), ← lift_union hdR] at hin
  rw [insert_union_comm hdR hxR]
  exact HasType.parr hin (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁, hxR⟩)

/-- Preservation for the left selection commuting conversion. -/
private theorem HasType.step_commSelectLeft {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q : Proc Atom}
    (h : HasType Γ (.cut c (.selectLeft (PiCalculus.liftName 0 x) p) q)) :
    HasType Γ (.selectLeft x (.cut c p q)) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, a, b, he, hp, hx⟩ := hl.selectLeft_inv
  obtain ⟨G₁, rfl, hxG₁, rfl⟩ := peel_cut_context hx he
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hp' : HasType ((Context.lift (G₁.insert x a)).insert (.var 0) c) p := by
    rw [lift_insert, insert_insert_comm (liftName_zero_ne_var_zero x)]
    exact hp
  have hin := HasType.cut hp' hr (disjoint_insert_of hxR hdR)
  rw [insert_union_comm hdR hxR] at hin
  rw [insert_union_comm hdR hxR]
  exact HasType.oplusLeft hin (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁, hxR⟩)

/-- Preservation for the right selection commuting conversion. -/
private theorem HasType.step_commSelectRight {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q : Proc Atom}
    (h : HasType Γ (.cut c (.selectRight (PiCalculus.liftName 0 x) p) q)) :
    HasType Γ (.selectRight x (.cut c p q)) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, a, b, he, hp, hx⟩ := hl.selectRight_inv
  obtain ⟨G₁, rfl, hxG₁, rfl⟩ := peel_cut_context hx he
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hp' : HasType ((Context.lift (G₁.insert x b)).insert (.var 0) c) p := by
    rw [lift_insert, insert_insert_comm (liftName_zero_ne_var_zero x)]
    exact hp
  have hin := HasType.cut hp' hr (disjoint_insert_of hxR hdR)
  rw [insert_union_comm hdR hxR] at hin
  rw [insert_union_comm hdR hxR]
  exact HasType.oplusRight hin (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁, hxR⟩)

/-- Preservation for the choice commuting conversion. -/
private theorem HasType.step_commChoice {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q r : Proc Atom}
    (h : HasType Γ (.cut c (.choice (PiCalculus.liftName 0 x) p q) r)) :
    HasType Γ (.choice x (.cut c p r) (.cut c q r)) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, a, b, he, hp, hq, hx⟩ := hl.choice_inv
  obtain ⟨G₁, rfl, hxG₁, rfl⟩ := peel_cut_context hx he
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hp' : HasType ((Context.lift (G₁.insert x a)).insert (.var 0) c) p := by
    rw [lift_insert, insert_insert_comm (liftName_zero_ne_var_zero x)]
    exact hp
  have hq' : HasType ((Context.lift (G₁.insert x b)).insert (.var 0) c) q := by
    rw [lift_insert, insert_insert_comm (liftName_zero_ne_var_zero x)]
    exact hq
  have hinp := HasType.cut hp' hr (disjoint_insert_of hxR hdR)
  have hinq := HasType.cut hq' hr (disjoint_insert_of hxR hdR)
  rw [insert_union_comm hdR hxR] at hinp hinq
  rw [insert_union_comm hdR hxR]
  exact HasType.with hinp hinq (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁, hxR⟩)

/-- Preservation for the `⊥` commuting conversion. -/
private theorem HasType.step_commBot {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {p q : Proc Atom}
    (h : HasType Γ (.cut c (.emptyInput (PiCalculus.liftName 0 x) p) q)) :
    HasType Γ (.emptyInput x (.cut c p q)) := by
  obtain ⟨G, R, rfl, hl, hr, hd⟩ := h.cut_inv
  obtain ⟨X, he, hp, hx⟩ := hl.emptyInput_inv
  obtain ⟨G₁, rfl, hxG₁, rfl⟩ := peel_cut_context hx he
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  have hin := HasType.cut hp hr hdR
  rw [insert_union_comm hdR hxR]
  exact HasType.bot hin (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁, hxR⟩)

/-- Preservation for the `⊤` commuting conversion. -/
private theorem HasType.step_commTop {Γ : Context Atom}
    {c : Logic.CLL.Proposition Atom} {x : PiCalculus.Name} {q : Proc Atom}
    (h : HasType Γ (.cut c (.emptyChoice (PiCalculus.liftName 0 x)) q)) :
    HasType Γ (.emptyChoice x) := by
  obtain ⟨G, R, rfl, hl, _, hd⟩ := h.cut_inv
  obtain ⟨X, he, hx⟩ := hl.emptyChoice_inv
  obtain ⟨G₁, rfl, hxG₁, -⟩ := peel_cut_context hx he
  obtain ⟨hxR, hdR⟩ := disjoint_insert_left hd
  rw [insert_union_comm hdR hxR]
  exact HasType.top (by rw [Finmap.mem_union, not_or]; exact ⟨hxG₁, hxR⟩)

/-- Type preservation for one-step reduction (Wadler, Theorem 1). -/
theorem HasType.preservation {Γ : Context Atom} {p q : Proc Atom}
    (h : HasType Γ p) (hstep : Step p q) : HasType Γ q := by
  induction hstep generalizing Γ with
  | axCut a w p => exact h.step_axCut
  | axCutSymm a w p => exact h.step_axCutSymm
  | tensorParr a b p q r => exact h.step_tensorParr
  | oplusWithLeft a b p q r => exact h.step_oplusWithLeft
  | oplusWithRight a b p q r => exact h.step_oplusWithRight
  | oneBot p => exact h.step_oneBot
  | commTensorLeft c x p q r hz => exact h.step_commTensorLeft hz
  | commTensorRight c x p q r hz => exact h.step_commTensorRight hz
  | commParr c x p q => exact h.step_commParr
  | commSelectLeft c x p q => exact h.step_commSelectLeft
  | commSelectRight c x p q => exact h.step_commSelectRight
  | commChoice c x p q r => exact h.step_commChoice
  | commBot c x p q => exact h.step_commBot
  | commTop c x q => exact h.step_commTop
  | cutLeft a _ q ih =>
    obtain ⟨X, Y, rfl, hp, hq, hd⟩ := h.cut_inv
    exact HasType.cut (ih hp) hq hd
  | cutRight a p _ ih =>
    obtain ⟨X, Y, rfl, hp, hq, hd⟩ := h.cut_inv
    exact HasType.cut hp (ih hq) hd
  | cong h₁ _ h₃ ih => exact (Cong.hasType_iff h₃).mp (ih ((Cong.hasType_iff h₁).mp h))

/-- Type preservation for multi-step reduction. -/
theorem HasType.preservation_steps {Γ : Context Atom} {p q : Proc Atom}
    (h : HasType Γ p) (hsteps : Steps p q) : HasType Γ q := by
  induction hsteps with
  | refl => exact h
  | tail _ hs ih => exact ih.preservation hs

/-- Every one-step reduction starts from a cut; a necessary condition
only (not every cut reduces). -/
theorem Step.isCut {p q : Proc Atom} (h : Step p q) :
    ∃ a p₁ p₂, p = .cut a p₁ p₂ := by
  induction h with
  | cong h₁ _ _ ih => exact (Cong.isCut_iff h₁).mpr ih
  | _ => exact ⟨_, _, _, rfl⟩

end Cslib.ClassicalProcesses
