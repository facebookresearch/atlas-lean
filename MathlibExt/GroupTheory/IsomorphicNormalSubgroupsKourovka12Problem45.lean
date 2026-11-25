/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Groups isomorphic to all their nontrivial normal subgroups (Kourovka Notebook Problem 12.45)

Kourovka Notebook, Archive of Solved Problems, Problem 12.45 (P. Hall; J. C. Lennox): must a
non-trivial group which is isomorphic to each of its non-trivial normal subgroups be free of
infinite rank, simple, or infinite cyclic?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.45 (P. Hall;
J. C. Lennox). UnsolvedMath record UM-00700864 (`KOU-12.45`), dataset ulamai/UnsolvedMath v1.8.0.

Free of infinite rank means isomorphic to the free group on an infinite type; simple is
`IsSimpleGroup`; infinite cyclic is cyclic and infinite. The isomorphisms with the normal subgroups
are abstract.

The theorem `isoToNormalSubgroupsFreeSimpleOrCyclic_refuted` uses a direct limit of groups
`Aⁿ`, where `A` is the group of even permutations of finite support on the natural numbers.
In the embedding from row `n` to row `n + 1`, coordinate `j` acts on disjoint sets by all
the input permutations up to `j`. An input first active at `k` is therefore active at every
coordinate from `k` onward in the next row. Simplicity of `A` lets a normal subgroup extract
each such factor. Consequently the nontrivial normal subgroups are exactly the tails obtained
by padding rows with leading identities. Each tail is isomorphic to the whole direct limit.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45Wanted

/-- **Hall's question on groups isomorphic to their nontrivial normal subgroups (Kourovka 12.45).**
The statement that every nontrivial group that is isomorphic to each of its nontrivial normal
subgroups is free of infinite rank (isomorphic to the free group on an infinite set), simple, or
infinite cyclic. -/
def isoToNormalSubgroupsFreeSimpleOrCyclic : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G →
    (∀ N : Subgroup G, N.Normal → N ≠ ⊥ → Nonempty (N ≃* G)) →
    (∃ X : Type, Infinite X ∧ Nonempty (FreeGroup X ≃* G)) ∨ IsSimpleGroup G ∨
      (IsCyclic G ∧ Infinite G)

noncomputable section

open Equiv Equiv.Perm Function

-- Extending a finite alternating group to permutations of the natural numbers.
private def act {m : ℕ} (e : Fin m ↪ ℕ) :
    alternatingGroup (Fin m) →* Perm ℕ :=
  (viaEmbeddingHom e).comp (alternatingGroup _).subtype

private theorem via_comp {A B C : Type} (e : A ↪ B) (f : B ↪ C) (g : Perm A) :
    viaEmbedding (viaEmbedding g e) f = viaEmbedding g (e.trans f) := by
  ext z
  by_cases hz : z ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hz
    rw [viaEmbedding_apply]
    by_cases hy : y ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hy
      rw [viaEmbedding_apply]
      exact (viaEmbedding_apply g (e.trans f) x).symm
    · rw [viaEmbedding_apply_of_notMem _ _ _ hy, viaEmbedding_apply_of_notMem]
      rintro ⟨x, hx⟩
      exact hy ⟨x, f.injective hx⟩
  · rw [viaEmbedding_apply_of_notMem _ _ _ hz, viaEmbedding_apply_of_notMem]
    rintro ⟨x, rfl⟩
    exact hz ⟨e x, rfl⟩

private theorem act_le {m n : ℕ} (e : Fin m ↪ ℕ) (f : Fin n ↪ ℕ)
    (h : Set.range e ⊆ Set.range f) : (act e).range ≤ (act f).range := by
  classical
  let j : Fin m ↪ Fin n := ⟨fun i => (h ⟨i, rfl⟩).choose, fun i k he => e.injective <| by
    have hi := (h (Set.mem_range_self i)).choose_spec
    have hk := (h (Set.mem_range_self k)).choose_spec
    exact hi.symm.trans ((congrArg f he).trans hk)⟩
  have hj : j.trans f = e := by ext i; exact (h (Set.mem_range_self i)).choose_spec
  rintro _ ⟨g, rfl⟩
  refine ⟨⟨viaEmbedding g.val j, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup, viaEmbedding, sign_extendDomain]
    exact mem_alternatingGroup.mp g.property
  · exact (via_comp j f g.val).trans (by rw [hj]; rfl)

private def initial (n : ℕ) : Fin n ↪ ℕ := Fin.valEmbedding

private theorem bounded {m : ℕ} (e : Fin m ↪ ℕ) :
    ∃ n, Set.range e ⊆ Set.range (initial n) := by
  obtain ⟨b, hb⟩ := (Set.finite_range e).bddAbove
  exact ⟨b + 1, fun i hi => ⟨⟨i, by have := hb hi; omega⟩, rfl⟩⟩

private theorem initial_mono : Monotone (fun n => (act (initial n)).range) := by
  intro n m h
  apply act_le
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castLE h, rfl⟩

private def finAlt : Subgroup (Perm ℕ) := ⨆ n, (act (initial n)).range

private theorem mem_finAlt {g : Perm ℕ} :
    g ∈ finAlt ↔ ∃ n, g ∈ (act (initial n)).range :=
  Subgroup.mem_iSup_of_directed initial_mono.directed_le

private def blockIn (n : ℕ) : alternatingGroup (Fin n) →* finAlt :=
  (act (initial n)).codRestrict _ fun g => mem_finAlt.mpr ⟨n, g, rfl⟩

private theorem blockIn_inj (n : ℕ) : Injective (blockIn n) :=
  fun _ _ h => Subtype.ext <| viaEmbeddingHom_injective _ (congrArg Subtype.val h)

private theorem commonBlock (x y : finAlt) :
    ∃ n ≥ 5, x ∈ (blockIn n).range ∧ y ∈ (blockIn n).range := by
  obtain ⟨i, hi⟩ := mem_finAlt.mp x.property
  obtain ⟨j, hj⟩ := mem_finAlt.mp y.property
  let n := i + j + 5
  obtain ⟨a, ha⟩ := initial_mono (show i ≤ n by dsimp [n]; omega) hi
  obtain ⟨b, hb⟩ := initial_mono (show j ≤ n by dsimp [n]; omega) hj
  exact ⟨n, by dsimp [n]; omega, ⟨a, Subtype.ext ha⟩, b, Subtype.ext hb⟩

private instance finAltNontrivial : Nontrivial finAlt := by
  let := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  exact (blockIn_inj 5).nontrivial

private instance finAltSimple : IsSimpleGroup finAlt where
  eq_bot_or_eq_top_of_normal N _ := by
    by_cases h : N = ⊥
    · exact Or.inl h
    right
    obtain ⟨⟨x, hx⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    have hx1 : x ≠ 1 := fun he => hne (Subtype.ext he)
    apply top_unique
    intro y _
    obtain ⟨n, hn, ⟨a, rfl⟩, ⟨b, rfl⟩⟩ := commonBlock x y
    let := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
    have htop := (Subgroup.Normal.eq_bot_or_eq_top (N.comap (blockIn n))).resolve_left (by
      intro he
      have ha : a ∈ N.comap (blockIn n) := hx
      rw [he, Subgroup.mem_bot] at ha
      simp [ha] at hx1)
    exact (show b ∈ N.comap (blockIn n) from htop ▸ Subgroup.mem_top b)

private def localize (e : ℕ ↪ ℕ) : finAlt →* finAlt :=
  ((viaEmbeddingHom e).comp finAlt.subtype).codRestrict _ fun x => by
    obtain ⟨n, g, hg⟩ := mem_finAlt.mp x.property
    change viaEmbedding x.val e ∈ finAlt
    rw [← hg]
    change viaEmbedding (viaEmbedding g.val (initial n)) e ∈ finAlt
    rw [via_comp]
    obtain ⟨m, hm⟩ := bounded ((initial n).trans e)
    exact mem_finAlt.mpr ⟨m, act_le _ _ hm ⟨g, rfl⟩⟩

-- The even and odd positions support two commuting copies of the finitary alternating group.
private def evenSlot : ℕ ↪ ℕ := ⟨(2 * ·), fun _ _ h => by dsimp at h; omega⟩
private def oddSlot : ℕ ↪ ℕ := ⟨fun i => 2 * i + 1, fun _ _ h => by dsimp at h; omega⟩

private theorem slot_disjoint (i j : ℕ) : evenSlot i ≠ oddSlot j := by
  change 2 * i ≠ 2 * j + 1
  omega

private theorem localize_at (e : ℕ ↪ ℕ) (x : finAlt) (i : ℕ) :
    (localize e x).val (e i) = e (x.val i) := viaEmbedding_apply ..

private theorem localize_off (e : ℕ ↪ ℕ) (x : finAlt) {i : ℕ} (hi : i ∉ Set.range e) :
    (localize e x).val i = i := viaEmbedding_apply_of_notMem _ _ _ hi

private theorem odd_at_even (x : finAlt) (i : ℕ) :
    (localize oddSlot x).val (evenSlot i) = evenSlot i :=
  localize_off _ _ fun ⟨j, hj⟩ => slot_disjoint i j hj.symm

private theorem even_at_odd (x : finAlt) (i : ℕ) :
    (localize evenSlot x).val (oddSlot i) = oddSlot i :=
  localize_off _ _ fun ⟨j, hj⟩ => slot_disjoint j i hj

private def merge : finAlt × finAlt →* finAlt :=
  MonoidHom.noncommCoprod (localize evenSlot) (localize oddSlot) fun x y => by
    apply Subtype.ext
    ext i
    change (localize evenSlot x).val ((localize oddSlot y).val i) =
      (localize oddSlot y).val ((localize evenSlot x).val i)
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · have he : i = evenSlot k := by change i = 2 * k; omega
      rw [he, odd_at_even, localize_at, odd_at_even]
    · have ho : i = oddSlot k := by change i = 2 * k + 1; omega
      rw [ho, even_at_odd, localize_at, even_at_odd]

private theorem merge_inj : Injective merge := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  apply Prod.ext
  · apply Subtype.ext
    ext i
    have he := congrArg (fun g : finAlt => g.val (evenSlot i)) h
    change (localize evenSlot a).val ((localize oddSlot b).val _) =
      (localize evenSlot c).val ((localize oddSlot d).val _) at he
    rw [odd_at_even, odd_at_even, localize_at, localize_at] at he
    exact evenSlot.injective he
  · apply Subtype.ext
    ext i
    have ho := congrArg (fun g : finAlt => g.val (oddSlot i)) h
    change (localize evenSlot a).val ((localize oddSlot b).val _) =
      (localize evenSlot c).val ((localize oddSlot d).val _) at ho
    rw [localize_at, localize_at, even_at_odd, even_at_odd] at ho
    exact oddSlot.injective ho

private theorem noncentral {x : finAlt} (hx : x ≠ 1) :
    ∃ y : finAlt, y * x * y⁻¹ * x⁻¹ ≠ 1 := by
  obtain ⟨n, hn, ⟨a, rfl⟩, _⟩ := commonBlock x 1
  by_contra! h
  have ha : a ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply blockIn_inj n
    simpa [map_mul, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] using h (blockIn n b)
  rw [alternatingGroup.center_eq_bot (by simp; omega), Subgroup.mem_bot] at ha
  simp [ha] at hx

private abbrev Row (n : ℕ) := Fin n → finAlt

-- A normal subgroup of a finite row contains each factor on which it acts nontrivially.
private theorem row_mem {n : ℕ} (N : Subgroup (Row n)) [N.Normal] {x : Row n}
    (hx : x ∈ N) (z : Row n) (hz : ∀ i, x i = 1 → z i = 1) : z ∈ N := by
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro i
  by_cases hi : x i = 1
  · simp [hz i hi]
  let f := MonoidHom.mulSingle (fun _ : Fin n => finAlt) i
  obtain ⟨y, hy⟩ := noncentral hi
  have hcomm : f (y * x i * y⁻¹ * (x i)⁻¹) = f y * x * (f y)⁻¹ * x⁻¹ := by
    ext j : 1
    by_cases hj : j = i
    · subst j
      simp [f]
    · simp [f, Pi.mulSingle_eq_of_ne hj]
  have hmem : y * x i * y⁻¹ * (x i)⁻¹ ∈ N.comap f := by
    rw [Subgroup.mem_comap, hcomm]
    exact N.mul_mem ((inferInstance : N.Normal).conj_mem _ hx _) (N.inv_mem hx)
  have ht := (Subgroup.Normal.eq_bot_or_eq_top (N.comap f)).resolve_left (fun he =>
    hy (Subgroup.mem_bot.mp (he ▸ hmem)))
  exact (show z i ∈ N.comap f from ht ▸ Subgroup.mem_top _)

-- Each output coordinate records the whole input prefix, using disjoint permutation supports.
private def entry {n : ℕ} (i : ℕ) : Row n →* finAlt :=
  if h : i < n then Pi.evalMonoidHom _ ⟨i, h⟩ else 1

private def pack {n : ℕ} : ℕ → Row n →* finAlt
  | 0 => 1
  | i + 1 => merge.comp ((pack i).prod (entry i))

private def advance (n : ℕ) : Row n →* Row (n + 1) :=
  MonoidHom.pi fun j => pack (j.val + 1)

private def Blank {n : ℕ} (k : ℕ) (x : Row n) : Prop :=
  ∀ i : Fin n, i.val < k → x i = 1

private theorem pack_eq_one {n : ℕ} (x : Row n) (k : ℕ) :
    pack k x = 1 ↔ Blank k x := by
  induction k with
  | zero => simp [pack, Blank]
  | succ k ih =>
    change merge (pack k x, entry k x) = 1 ↔ _
    rw [← merge.map_one, merge_inj.eq_iff, Prod.mk_eq_one, ih]
    constructor
    · rintro ⟨h, he⟩ i hi
      by_cases hik : i.val < k
      · exact h i hik
      · have hik' : i.val = k := by omega
        subst k
        simpa [entry, i.isLt] using he
    · intro h
      refine ⟨fun i hi => h i (by omega), ?_⟩
      by_cases hk : k < n
      · simpa [entry, hk] using h ⟨k, hk⟩ (by simp)
      · simp [entry, hk]

private theorem advance_blank {n : ℕ} (x : Row n) (k : ℕ) :
    Blank k (advance n x) ↔ Blank k x := by
  constructor
  · intro h i hi
    have := (pack_eq_one x (i.val + 1)).mp (h i.castSucc hi)
    exact this i (by simp)
  · intro h i hi
    exact (pack_eq_one x (i.val + 1)).mpr fun j hj => h j (by omega)

private theorem advance_inj (n : ℕ) : Injective (advance n) := by
  apply (injective_iff_map_eq_one (advance n)).mpr
  intro x hx
  funext i
  exact ((advance_blank x n).mp (by rw [hx]; intro _ _; rfl)) i i.isLt

private def transition (n m : ℕ) (h : n ≤ m) : Row n →* Row m :=
  Nat.leRecOn (motive := fun j => Row n →* Row j) h
    (fun f => (advance _).comp f) (MonoidHom.id _)

private theorem transition_self (n : ℕ) : transition n n le_rfl = .id _ :=
  Nat.leRecOn_self _

private theorem transition_succ {n m : ℕ} (h : n ≤ m) :
    transition n (m + 1) (by omega) = (advance m).comp (transition n m h) :=
  Nat.leRecOn_succ h _

private instance rowDirected : DirectedSystem Row (transition · · ·) where
  map_self x := by simp [transition_self]
  map_map {k j i} hij hjk x := by
    induction k, hjk using Nat.le_induction with
    | base => simp [transition_self]
    | succ k h ih => simp only [transition_succ h, transition_succ (hij.trans h),
        MonoidHom.comp_apply, ih]

private theorem transition_blank {n m : ℕ} (h : n ≤ m) (x : Row n) (k : ℕ) :
    Blank k (transition n m h x) ↔ Blank k x := by
  induction m, h using Nat.le_induction with
  | base => simp [transition_self]
  | succ m h ih => simpa only [transition_succ h, MonoidHom.comp_apply, advance_blank] using ih

private abbrev LimitGroup := DirectLimit Row transition

private def insertRow (n : ℕ) : Row n →* LimitGroup where
  toFun x := ⟦⟨n, x⟩⟧
  map_one' := (DirectLimit.one_def n).symm
  map_mul' x y := (DirectLimit.mul_def n x y).symm

private theorem insert_inj (n : ℕ) : Injective (insertRow n) := by
  refine DirectLimit.mk_injective transition ?_ n
  intro i j h
  induction j, h using Nat.le_induction with
  | base => simpa only [transition_self, MonoidHom.coe_id] using injective_id
  | succ j h ih => exact transition_succ h ▸ (advance_inj j).comp ih

private theorem insert_transition {n m : ℕ} (h : n ≤ m) (x : Row n) :
    insertRow m (transition n m h x) = insertRow n x :=
  DirectLimit.mk_apply (f := transition) n m x h

private theorem insert_advance {n : ℕ} (x : Row n) :
    insertRow (n + 1) (advance n x) = insertRow n x := by
  simpa [transition_succ (le_refl n), transition_self] using
    insert_transition (Nat.le_succ n) x

-- Padding each row with k leading identities induces the shift endomorphism of the limit.
private def pad (k n : ℕ) : Row n →* Row (k + n) :=
  MonoidHom.pi fun i => if h : k ≤ i.val then
    Pi.evalMonoidHom _ ⟨i.val - k, by omega⟩ else 1

private theorem entry_pad {k n : ℕ} (x : Row n) (j : ℕ) :
    entry (j + k) (pad k n x) = entry j x := by
  by_cases h : j < n
  · simp [entry, pad, h, show j + k < k + n by omega]
  · simp [entry, h, show ¬ j + k < k + n by omega]

private theorem pack_pad_before {k n : ℕ} (x : Row n) {j : ℕ} (h : j ≤ k) :
    pack j (pad k n x) = 1 :=
  (pack_eq_one _ _).mpr fun i hi => by simp [pad, show ¬ k ≤ i.val by omega]

private theorem pack_pad {k n : ℕ} (x : Row n) (j : ℕ) :
    pack (j + k) (pad k n x) = pack j x := by
  induction j with
  | zero => simpa [pack] using pack_pad_before x (le_refl k)
  | succ j ih =>
    rw [Nat.succ_add]
    simp only [pack, MonoidHom.comp_apply, MonoidHom.prod_apply, ih, entry_pad]

private theorem pad_advance {n : ℕ} (k : ℕ) (x : Row n) :
    pad k (n + 1) (advance n x) = advance (k + n) (pad k n x) := by
  funext i
  change (if h : k ≤ i.val then Pi.evalMonoidHom (fun _ : Fin (n + 1) => finAlt)
    ⟨i.val - k, by omega⟩ else 1) (advance n x) = pack (i.val + 1) (pad k n x)
  split_ifs with h
  · change pack (i.val - k + 1) x = _
    rw [show i.val + 1 = (i.val - k + 1)+k by omega, pack_pad]
  · exact (pack_pad_before x (by omega)).symm

private def shiftedRow (k n : ℕ) : Row n →* LimitGroup := (insertRow (k + n)).comp (pad k n)

private theorem shifted_succ (k n : ℕ) (x : Row n) :
    shiftedRow k (n + 1) (advance n x) = shiftedRow k n x := by
  change insertRow _ (pad _ _ _) = insertRow _ _
  rw [pad_advance]
  exact insert_advance _

private theorem shifted_compat (k n m : ℕ) (h : n ≤ m) (x : Row n) :
    shiftedRow k n x = shiftedRow k m (transition n m h x) := by
  induction m, h using Nat.le_induction with
  | base => simp [transition_self]
  | succ m h ih => simpa only [transition_succ h, MonoidHom.comp_apply, shifted_succ] using ih

private def shift (k : ℕ) : LimitGroup →* LimitGroup where
  toFun := DirectLimit.lift transition (fun n => shiftedRow k n) (shifted_compat k)
  map_one' := by nth_rw 1 [← (insertRow 0).map_one]; exact (shiftedRow k 0).map_one
  map_mul' := DirectLimit.lift_mul (shiftedRow k) _

private theorem shift_insert (k n : ℕ) (x : Row n) :
    shift k (insertRow n x) = insertRow (k + n) (pad k n x) := rfl

private theorem shift_inj (k : ℕ) : Injective (shift k) := by
  refine DirectLimit.lift_injective transition (fun n => shiftedRow k n) (shifted_compat k) ?_
  intro n a b he
  have hab : pad k n a = pad k n b := insert_inj (k + n) he
  funext i
  have := congrFun hab (⟨i.val + k, by omega⟩ : Fin (k + n))
  simpa [pad] using this

private def tailPred (k : ℕ) : LimitGroup → Prop :=
  DirectLimit.lift transition (fun _ => Blank k)
    fun _ _ h x => propext (transition_blank h x k).symm

private theorem tail_insert (k n : ℕ) (x : Row n) :
    tailPred k (insertRow n x) ↔ Blank k x := Iff.rfl

private theorem range_iff_tail (k : ℕ) (g : LimitGroup) :
    g ∈ (shift k).range ↔ tailPred k g := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk transition y
    change Blank k (pad k n x)
    intro i hi
    simp [pad, Nat.not_le.mpr hi]
  · obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk transition g
    change Blank k x → insertRow n x ∈ (shift k).range
    intro hx
    let z := transition n (k + n) (by omega) x
    have hz : Blank k z := (transition_blank _ x k).mpr hx
    let y : Row n := fun i => z ⟨i.val + k, by omega⟩
    have he : pad k n y = z := by
      funext i
      by_cases h : k ≤ i.val
      · simp [pad, h, y]
      · simpa [pad, h] using (hz i (by omega)).symm
    exact ⟨insertRow n y, (shift_insert k n y).trans (he ▸ insert_transition _ x)⟩

private instance tailNormal (k : ℕ) : (shift k).range.Normal where
  conj_mem a ha b := by
    obtain ⟨n, x, y, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ transition a b
    change insertRow n x ∈ _ at ha
    have hx := (tail_insert k n x).mp ((range_iff_tail k _).mp ha)
    change insertRow n y * insertRow n x * (insertRow n y)⁻¹ ∈ _
    rw [← map_inv, ← map_mul, ← map_mul, range_iff_tail, tail_insert]
    intro i hi
    simp [hx i hi]

-- Once a normal subgroup detects coordinate k, it contains the tail starting at k.
private theorem tail_le {N : Subgroup LimitGroup} [N.Normal] {n k : ℕ} {x : Row n}
    (hx : insertRow n x ∈ N) (hk : ¬ Blank (k + 1) x) : (shift k).range ≤ N := by
  intro g hg
  obtain ⟨m, y, rfl⟩ := DirectLimit.exists_eq_mk transition g
  have hy := (tail_insert k m y).mp ((range_iff_tail k _).mp hg)
  let t := max n m
  let x' := transition n t (le_max_left ..) x
  let y' := transition m t (le_max_right ..) y
  have hx' : ¬ Blank (k + 1) x' := fun h => hk ((transition_blank _ _ _).mp h)
  have hy' : Blank k (advance t y') := (advance_blank _ _).mpr ((transition_blank _ _ _).mpr hy)
  have hm : advance t x' ∈ N.comap (insertRow (t + 1)) := by
    simpa only [Subgroup.mem_comap, insert_advance, x', insert_transition] using hx
  have hr := row_mem _ hm (advance t y') (fun i hi => by
    apply hy' i
    by_contra! h
    exact hx' (fun j hj => (pack_eq_one x' (i.val + 1)).mp hi j (by omega)))
  change insertRow m y ∈ N
  simpa only [Subgroup.mem_comap, insert_advance, y', insert_transition] using hr

private theorem normal_is_tail (N : Subgroup LimitGroup) [N.Normal] (hne : N ≠ ⊥) :
    ∃ k, N = (shift k).range := by
  classical
  let P (k : ℕ) := ∃ (n : ℕ) (x : Row n) (i : Fin n), insertRow n x ∈ N ∧ i.val = k ∧ x i ≠ 1
  have hp : ∃ k, P k := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk transition g
    have hx : x ≠ 1 := by
      intro h
      apply hg1
      exact Subtype.ext (h ▸ (insertRow n).map_one)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact ⟨i.val, n, x, i, hg, rfl, hi⟩
  let k := Nat.find hp
  obtain ⟨n, x, i, hx, hik, hi⟩ := Nat.find_spec hp
  have hik' : i.val = k := hik
  have hactive : ¬ Blank (k + 1) x := fun h => hi (h i (by omega))
  refine ⟨k, le_antisymm ?_ (tail_le hx hactive)⟩
  intro g hg
  obtain ⟨m, y, rfl⟩ := DirectLimit.exists_eq_mk transition g
  rw [range_iff_tail]
  change Blank k y
  intro j hj
  by_contra h
  exact Nat.find_min hp hj ⟨m, y, j, hg, rfl, h⟩

private def firstFactor : finAlt →* LimitGroup :=
  (insertRow 1).comp (MonoidHom.pi fun _ => MonoidHom.id finAlt)

private theorem firstFactor_inj : Injective firstFactor := by
  intro x y h
  exact congrFun (insert_inj 1 h) 0

private instance limitNontrivial : Nontrivial LimitGroup := firstFactor_inj.nontrivial

private theorem limit_not_simple : ¬ IsSimpleGroup LimitGroup := by
  intro h
  rcases Subgroup.Normal.eq_bot_or_eq_top (shift 1).range with hb | ht
  · obtain ⟨x, hx⟩ := exists_ne (1 : LimitGroup)
    have hm : shift 1 x ∈ (shift 1).range := ⟨x, rfl⟩
    rw [hb, Subgroup.mem_bot, ← (shift 1).map_one] at hm
    exact hx (shift_inj 1 hm)
  · obtain ⟨x, hx⟩ := exists_ne (1 : finAlt)
    have hm : firstFactor x ∈ (shift 1).range := ht ▸ Subgroup.mem_top _
    exact hx (((range_iff_tail 1 _).mp hm : Blank 1 (fun _ : Fin 1 => x)) 0 Nat.zero_lt_one)

private theorem limit_not_free (X : Type) (e : FreeGroup X ≃* LimitGroup) : False := by
  let := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  let f := e.symm.toMonoidHom.comp (firstFactor.comp (blockIn 5))
  have hf : Injective f := e.symm.injective.comp (firstFactor_inj.comp (blockIn_inj 5))
  obtain ⟨n, hn, he⟩ := (f.isOfFinOrder (isOfFinOrder_of_finite a)).exists_pow_eq_one
  have hfa : f a = 1 := (pow_eq_one_iff_left hn.ne').mp he
  exact ha (hf (hfa.trans f.map_one.symm))

private theorem limit_not_cyclic : ¬ IsCyclic LimitGroup := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (1 : finAlt)
  obtain ⟨b, hb⟩ := noncentral ha
  apply hb
  apply firstFactor_inj
  have hc := h.isMulCommutative
  simp only [map_mul, map_inv, map_one]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact mul_comm' _ _

end

/--
**A group isomorphic to its nontrivial normal subgroups need not be free of infinite rank, simple
or infinite cyclic.** There is a nontrivial group $G$ that is isomorphic to each of its nontrivial
normal subgroups and is neither free of infinite rank (isomorphic to the free group on an infinite
set), nor simple, nor infinite cyclic. That is, the answer to Kourovka Problem 12.45 is negative
(V. N. Obraztsov, 1997).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 12.45 (P. Hall; J. C. Lennox); resolution: V. N. Obraztsov, Proc. London Math. Soc. (3) 75
(1997), 79-98, Kourovka Archive, Problem 12.45: No.
-/
theorem isoToNormalSubgroupsFreeSimpleOrCyclic_refuted :
    ¬ isoToNormalSubgroupsFreeSimpleOrCyclic := by
  intro hall
  have hnormal (N : Subgroup LimitGroup) (hn : N.Normal) (hne : N ≠ ⊥) :
      Nonempty (N ≃* LimitGroup) := by
    obtain ⟨k, rfl⟩ := normal_is_tail N hne
    exact ⟨(MonoidHom.ofInjective (shift_inj k)).symm⟩
  rcases hall LimitGroup inferInstance hnormal with ⟨X, _, ⟨e⟩⟩ | hs | ⟨hc, _⟩
  · exact limit_not_free X e
  · exact limit_not_simple hs
  · exact limit_not_cyclic hc

end MathlibExt.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45Wanted
