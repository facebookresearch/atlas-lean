/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import CSLibExt.MachineLearning.GraphicalModels.MarkovEquivalence
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Extension.Linear

/-!
# Verma and Pearl: Markov-equivalent structures have the same d-separations

Verma and Pearl (1990, "Equivalence and synthesis of causal models",
Theorem 1) characterize Markov equivalence of DAGs by skeleton and
v-structures. This file proves the direction that Markov-equivalent
structures induce the same d-separations, working with parent-set
structures `Pa : V → Finset V` and the parent-set mirror `DSeparatedPa` of
`BayesNet.DSeparated`.

## Main results

* `dSeparatedPa_iff_of_coveredReversal`: one covered-edge reversal of an
  acyclic structure preserves every d-separation (proved by transporting
  unblocked paths across the reversal).
* `dSeparatedPa_iff_of_markovEquivalent`: two acyclic structures with the
  same skeleton and the same v-structures have the same d-separations, by
  induction along a covered-reversal sequence from Chickering's
  transformational characterization (`MarkovEquivalence.lean`).
* `BayesNet.dSeparated_iff_of_markovEquivalent`: the corollary for Bayesian
  networks, with d-separations transported along a relabeling.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset BayesianDirichlet

variable {α β : Type*}

/-! ### Definition 1: the parent-set mirror of the `BayesNet` d-separation family

Each definition is its `BayesNet` counterpart with `u ∈ Pa v` for `b.Edge u v` and
`Adjacent Pa` for `b.Adj`. -/

/-- `j` is a descendant of `i` in `Pa` (every node is its own descendant). Mirrors
`BayesNet.IsDescendant`. -/
def IsDescendantPa {V : Type*} (Pa : V → Finset V) (i j : V) : Prop :=
  Relation.ReflTransGen (fun u w => u ∈ Pa w) i j

/-- A path of the skeleton of `Pa` from `x` to `y`: a list of distinct nodes, consecutive ones
adjacent, starting at `x` and ending at `y`. Mirrors `BayesNet.IsPath`. -/
def IsPathPa {V : Type*} (Pa : V → Finset V) (x y : V) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain (Adjacent Pa) ∧ p.head? = some x ∧ p.getLast? = some y

/-- The consecutive nodes `u, m, w` of a path are blocked by `Z`: either `m` is a collider
`u → m ← w` none of whose descendants is in `Z`, or `m` is not a collider and `m ∈ Z`. Mirrors
`BayesNet.BlockedAt`. -/
def BlockedAtPa {V : Type*} (Pa : V → Finset V) (Z : Set V) (u m w : V) : Prop :=
  (u ∈ Pa m ∧ w ∈ Pa m ∧ ∀ d, IsDescendantPa Pa m d → d ∉ Z) ∨
    (¬(u ∈ Pa m ∧ w ∈ Pa m) ∧ m ∈ Z)

/-- A path is blocked by `Z` if some three consecutive nodes of it are. Mirrors
`BayesNet.PathBlocked`. -/
def PathBlockedPa {V : Type*} (Pa : V → Finset V) (Z : Set V) (p : List V) : Prop :=
  ∃ (i : ℕ) (h : i + 2 < p.length), BlockedAtPa Pa Z p[i] p[i + 1] p[i + 2]

/-- **d-separation** in `Pa`: `Z` d-separates `X` from `Y` if every path between a node of `X`
and a node of `Y` is blocked by `Z`. Mirrors `BayesNet.DSeparated`; `X`, `Y`, `Z` are arbitrary,
possibly overlapping sets. -/
def DSeparatedPa {V : Type*} (Pa : V → Finset V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ p, IsPathPa Pa x y p → PathBlockedPa Pa Z p

/-! ### Definitions 2-4: the structure of a network, relabeling, and the carrier -/

/-- Definition 2. The parent-set structure of a network: the parents of `k` are the `i` with
`b.Edge i k`. -/
def BayesNet.toPa {n : ℕ} (b : BayesNet α n) : Fin n → Finset (Fin n) :=
  fun k => univ.filter (b.Edge · k)

/-- Definition 3. Transport a structure along `e : V ≃ W`: the parents of `w` are the images of
the parents of `e.symm w`. -/
def relabel {V W : Type*} (e : V ≃ W) (Pa : V → Finset V) : W → Finset W :=
  fun w => (Pa (e.symm w)).map e.toEmbedding

/-- Definition 4. The carrier parent map on `Fin m` for `e : V ≃ Fin m`, meant for `e`
topological for `Pa` (`u ∈ Pa v → e u < e v`): node `k` gets the parents `j < k` with
`e.symm j ∈ Pa (e.symm k)`. -/
def paOf {V : Type*} [DecidableEq V] {m : ℕ} (e : V ≃ Fin m) (Pa : V → Finset V) :
    (k : Fin m) → Finset (Fin k) :=
  fun k => univ.filter fun j => e.symm (Fin.castLE k.2.le j) ∈ Pa (e.symm k)

/-! ### T1: the structure of a network -/

/-- (parents). -/
theorem BayesNet.mem_toPa {n : ℕ} (b : BayesNet α n) {i j : Fin n} :
    i ∈ b.toPa j ↔ b.Edge i j := by simp [BayesNet.toPa]

/-- (acyclicity). The structure of a network is acyclic. -/
theorem isAcyclic_toPa {n : ℕ} (b : BayesNet α n) : IsAcyclic b.toPa := by
  intro v hv
  have hmono : ∀ {a c : Fin n},
      Relation.TransGen (fun u w => u ∈ b.toPa w) a c → a.val < c.val := by
    intro a c h
    induction h with
    | single hmem =>
      obtain ⟨hlt, -⟩ := (BayesNet.mem_toPa b).mp hmem
      exact hlt
    | tail _ hmem ih =>
      obtain ⟨hlt2, -⟩ := (BayesNet.mem_toPa b).mp hmem
      exact Nat.lt_trans ih hlt2
  exact absurd (hmono hv) (lt_irrefl _)

/-- (skeleton). -/
theorem adjacent_toPa_iff {n : ℕ} (b : BayesNet α n) {i j : Fin n} :
    Adjacent b.toPa i j ↔ b.Adj i j := by
  simp only [Adjacent, BayesNet.Adj, BayesNet.mem_toPa]

/-! ### T2: bridge from `BayesNet` to parent-set structures -/

/-- d-separation in a network is d-separation in its structure. -/
theorem BayesNet.dSeparated_iff_dSeparatedPa_toPa {n : ℕ} (b : BayesNet α n)
    {X Y Z : Set (Fin n)} : b.DSeparated X Y Z ↔ DSeparatedPa b.toPa X Y Z := by
  have hedge : (fun u w : Fin n => u ∈ b.toPa w) = b.Edge :=
    funext fun u => funext fun w => propext (BayesNet.mem_toPa b)
  have hadj : Adjacent b.toPa = b.Adj :=
    funext fun i => funext fun j => propext (adjacent_toPa_iff b)
  unfold BayesNet.DSeparated DSeparatedPa BayesNet.IsPath IsPathPa BayesNet.PathBlocked
    PathBlockedPa BayesNet.BlockedAt BlockedAtPa BayesNet.IsDescendant IsDescendantPa
  rw [hedge, hadj]
  simp only [BayesNet.mem_toPa]

/-! ### T3: relabeling -/

private theorem mem_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W) (u w : V) :
    e u ∈ relabel e Pa (e w) ↔ u ∈ Pa w := by
  unfold relabel
  simp [Equiv.symm_apply_apply]

private theorem mem_relabel_symm {V W : Type*} {Pa : V → Finset V} (e : V ≃ W) (x y : W) :
    x ∈ relabel e Pa y ↔ e.symm x ∈ Pa (e.symm y) := by
  simp [relabel]

private theorem transGen_relabel_of {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    {a b : V} (h : Relation.TransGen (fun u w => u ∈ Pa w) a b) :
    Relation.TransGen (fun u w => u ∈ relabel e Pa w) (e a) (e b) := by
  induction h with
  | single hmem => exact Relation.TransGen.single ((mem_relabel e _ _).mpr hmem)
  | tail _ hmem ih => exact ih.tail ((mem_relabel e _ _).mpr hmem)

private theorem transGen_of_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    {x y : W} (h : Relation.TransGen (fun u w => u ∈ relabel e Pa w) x y) :
    Relation.TransGen (fun u w => u ∈ Pa w) (e.symm x) (e.symm y) := by
  induction h with
  | single hmem => exact Relation.TransGen.single ((mem_relabel_symm e _ _).mp hmem)
  | tail _ hmem ih => exact ih.tail ((mem_relabel_symm e _ _).mp hmem)

private theorem reflTransGen_relabel_of {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    {a b : V} (h : Relation.ReflTransGen (fun u w => u ∈ Pa w) a b) :
    Relation.ReflTransGen (fun u w => u ∈ relabel e Pa w) (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hmem ih => exact ih.tail ((mem_relabel e _ _).mpr hmem)

private theorem reflTransGen_of_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    {x y : W} (h : Relation.ReflTransGen (fun u w => u ∈ relabel e Pa w) x y) :
    Relation.ReflTransGen (fun u w => u ∈ Pa w) (e.symm x) (e.symm y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hmem ih => exact ih.tail ((mem_relabel_symm e _ _).mp hmem)

private theorem isDescendantPa_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    (a b : V) : IsDescendantPa (relabel e Pa) (e a) (e b) ↔ IsDescendantPa Pa a b := by
  unfold IsDescendantPa
  constructor
  · intro h
    have h' := reflTransGen_of_relabel e h
    simpa [Equiv.symm_apply_apply] using h'
  · intro h
    exact reflTransGen_relabel_of e h

private theorem isDescendantPa_relabel_symm {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    (m : V) (d : W) :
    IsDescendantPa (relabel e Pa) (e m) d ↔ IsDescendantPa Pa m (e.symm d) := by
  unfold IsDescendantPa
  constructor
  · intro h
    have h' := reflTransGen_of_relabel e h
    simpa [Equiv.symm_apply_apply] using h'
  · intro h
    have h' := reflTransGen_relabel_of e h
    simpa [Equiv.apply_symm_apply] using h'

private theorem mem_image_relabel {V W : Type*} {Z : Set V} (e : V ≃ W) (a : V) :
    e a ∈ e '' Z ↔ a ∈ Z := by
  simp

private theorem mem_image_relabel_symm {V W : Type*} {Z : Set V} (e : V ≃ W) (d : W) :
    d ∈ e '' Z ↔ e.symm d ∈ Z := by
  constructor
  · intro h
    obtain ⟨x, hxZ, hxe⟩ := Set.mem_image e Z d |>.mp h
    have hx : x = e.symm d := by
      have h2 := congrArg e.symm hxe
      simpa [Equiv.symm_apply_apply] using h2
    rwa [hx] at hxZ
  · intro h
    exact Set.mem_image e Z d |>.mpr ⟨e.symm d, h, Equiv.apply_symm_apply e d⟩

private theorem blockedAtPa_relabel {V W : Type*} {Pa : V → Finset V} {Z : Set V}
    (e : V ≃ W) (u m w : V) :
    BlockedAtPa (relabel e Pa) (e '' Z) (e u) (e m) (e w) ↔
      BlockedAtPa Pa Z u m w := by
  unfold BlockedAtPa
  have hmem1 : e u ∈ relabel e Pa (e m) ↔ u ∈ Pa m := mem_relabel e u m
  have hmem2 : e w ∈ relabel e Pa (e m) ↔ w ∈ Pa m := mem_relabel e w m
  have hmemZ : e m ∈ e '' Z ↔ m ∈ Z := mem_image_relabel e m
  have hdesc : (∀ d : W, IsDescendantPa (relabel e Pa) (e m) d → d ∉ e '' Z) ↔
      (∀ d0 : V, IsDescendantPa Pa m d0 → d0 ∉ Z) := by
    constructor
    · intro H d0 hd hmem
      exact H (e d0) ((isDescendantPa_relabel e m d0).mpr hd)
        ((mem_image_relabel e d0).mpr hmem)
    · intro H d hd hmem
      exact H (e.symm d) ((isDescendantPa_relabel_symm e m d).mp hd)
        ((mem_image_relabel_symm e d).mp hmem)
  rw [hmem1, hmem2, hmemZ, hdesc]

private theorem isChain_map_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W)
    (q : List V) :
    (q.map e).IsChain (Adjacent (relabel e Pa)) ↔ q.IsChain (Adjacent Pa) := by
  induction q with
  | nil => simp
  | cons a q ih =>
    cases q with
    | nil => simp
    | cons b q' =>
      have hadj : Adjacent (relabel e Pa) (e a) (e b) ↔ Adjacent Pa a b := by
        simp [Adjacent, mem_relabel]
      have ih' : (e b :: q'.map e).IsChain (Adjacent (relabel e Pa)) ↔
          (b :: q').IsChain (Adjacent Pa) := ih
      simp [List.map_cons, List.isChain_cons_cons, hadj, ih']

private theorem nodup_map_relabel {V W : Type*} (e : V ≃ W) (q : List V) :
    (q.map e).Nodup ↔ q.Nodup :=
  List.nodup_map_iff (Equiv.injective e)

private theorem head_map_relabel {V W : Type*} (e : V ≃ W) (q : List V) (x : V) :
    (q.map e).head? = some (e x) ↔ q.head? = some x := by
  rw [List.head?_map]
  cases q.head? with
  | none => simp
  | some a => simp

private theorem getLast_map_relabel {V W : Type*} (e : V ≃ W) (q : List V) (y : V) :
    (q.map e).getLast? = some (e y) ↔ q.getLast? = some y := by
  rw [List.getLast?_map]
  cases q.getLast? with
  | none => simp
  | some a => simp

private theorem isPathPa_map {V W : Type*} {Pa : V → Finset V} (e : V ≃ W) (x y : V)
    (q : List V) :
    IsPathPa (relabel e Pa) (e x) (e y) (q.map e) ↔ IsPathPa Pa x y q := by
  unfold IsPathPa
  rw [nodup_map_relabel, isChain_map_relabel, head_map_relabel, getLast_map_relabel]

private theorem pathBlockedPa_map {V W : Type*} {Pa : V → Finset V} {Z : Set V}
    (e : V ≃ W) (q : List V) :
    PathBlockedPa (relabel e Pa) (e '' Z) (q.map e) ↔ PathBlockedPa Pa Z q := by
  unfold PathBlockedPa
  simp only [List.length_map]
  apply exists_congr
  intro i
  apply exists_congr
  intro h
  simp only [List.getElem_map]
  exact blockedAtPa_relabel e _ _ _

private theorem map_symm_map {V W : Type*} (e : V ≃ W) (p : List W) :
    (p.map e.symm).map e = p := by
  simp

private theorem map_map_symm {V W : Type*} (e : V ≃ W) (q : List V) :
    (q.map e).map e.symm = q := by
  simp

/-- d-separation is invariant under relabeling. -/
theorem dSeparatedPa_relabel {V W : Type*} {Pa : V → Finset V} {X Y Z : Set V} (e : V ≃ W) :
    DSeparatedPa (relabel e Pa) (e '' X) (e '' Y) (e '' Z) ↔ DSeparatedPa Pa X Y Z := by
  unfold DSeparatedPa
  constructor
  · intro H x hx y hy p hp
    have hx' : e x ∈ e '' X := (mem_image_relabel e x).mpr hx
    have hy' : e y ∈ e '' Y := (mem_image_relabel e y).mpr hy
    have hp' : IsPathPa (relabel e Pa) (e x) (e y) (p.map e) :=
      (isPathPa_map e x y p).mpr hp
    have hb' := H _ hx' _ hy' _ hp'
    exact (pathBlockedPa_map e p).mp hb'
  · intro H x hx y hy p hp
    obtain ⟨x0, hx0, rfl⟩ := (Set.mem_image e X x).mp hx
    obtain ⟨y0, hy0, rfl⟩ := (Set.mem_image e Y y).mp hy
    set q := p.map e.symm with hq
    have hp_eq : q.map e = p := map_symm_map e p
    have hp_qmap : IsPathPa (relabel e Pa) (e x0) (e y0) (q.map e) := by
      rw [hp_eq]
      exact hp
    have hp_q : IsPathPa Pa x0 y0 q := (isPathPa_map e x0 y0 q).mp hp_qmap
    have hb_q := H _ hx0 _ hy0 _ hp_q
    have hb_qmap : PathBlockedPa (relabel e Pa) (e '' Z) (q.map e) :=
      (pathBlockedPa_map e q).mpr hb_q
    rwa [hp_eq] at hb_qmap

/-- (skeleton). -/
theorem adjacent_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W) (u w : V) :
    Adjacent (relabel e Pa) (e u) (e w) ↔ Adjacent Pa u w := by
  simp only [Adjacent, mem_relabel]

/-- (v-structures). -/
theorem isVStructure_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W) (u w z : V) :
    IsVStructure (relabel e Pa) (e u) (e w) (e z) ↔ IsVStructure Pa u w z := by
  have hne : e u ≠ e z ↔ u ≠ z := (Equiv.injective e).ne_iff
  simp only [IsVStructure, mem_relabel, adjacent_relabel, hne]

/-- (acyclicity). -/
theorem isAcyclic_relabel {V W : Type*} {Pa : V → Finset V} (e : V ≃ W) :
    IsAcyclic (relabel e Pa) ↔ IsAcyclic Pa := by
  constructor
  · intro h v hv
    exact h (e v) (transGen_relabel_of e hv)
  · intro h w hw
    exact h (e.symm w) (transGen_of_relabel e hw)

/-! ### T4: bridge from parent-set structures to `BayesNet` (the carrier) -/

/-- (topological numbering). An acyclic structure on a finite type has a numbering in
which every parent precedes its child. -/
theorem exists_topological_equiv {V : Type*} [Fintype V] {Pa : V → Finset V}
    (h : IsAcyclic Pa) :
    ∃ e : V ≃ Fin (Fintype.card V), ∀ u v, u ∈ Pa v → e u < e v := by
  haveI : IsPartialOrder V
      (fun a b : V => Relation.ReflTransGen (fun x y => x ∈ Pa y) a b) :=
    { refl := fun a => Relation.ReflTransGen.refl
      trans := fun a b c hab hbc => hab.trans hbc
      antisymm := fun a b hab hba => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with h | hab'
        · exact h.symm
        · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with h | hba'
          · exact h
          · exact (h a (hab'.trans hba')).elim }
  obtain ⟨s, hs, hrs⟩ := extend_partialOrder
    (fun a b : V => Relation.ReflTransGen (fun x y => x ∈ Pa y) a b)
  letI : LinearOrder V :=
    { le := s
      le_refl := hs.1.1.1.1
      le_trans := hs.1.1.2.1
      le_antisymm := hs.1.2.1
      le_total := hs.2.1
      toDecidableLE := Classical.decRel _ }
  refine ⟨(monoEquivOfFin V rfl).symm.toEquiv, ?_⟩
  intro u v huv
  have hle : u ≤ v := hrs u v (Relation.ReflTransGen.single huv)
  have hne : u ≠ v := by
    rintro rfl
    exact h _ (Relation.TransGen.single huv)
  have hlt : u < v := lt_of_le_of_ne hle hne
  exact (monoEquivOfFin V rfl).symm.strictMono hlt

/-- (carrier). For `e` topological for `Pa`, a network with parents `paOf e Pa` (any value
type, any tables) has structure `relabel e Pa`. -/
theorem toPa_eq_relabel_of_pa_eq {V : Type*} [DecidableEq V] {m : ℕ} {Pa : V → Finset V}
    (b : BayesNet α m) (e : V ≃ Fin m) (he : ∀ u v, u ∈ Pa v → e u < e v) :
    b.pa = paOf e Pa → b.toPa = relabel e Pa := by
  intro hpa
  funext k
  ext i
  rw [BayesNet.mem_toPa, mem_relabel_symm]
  unfold BayesNet.Edge
  constructor
  · rintro ⟨hlt, hmem⟩
    rw [hpa] at hmem
    simp only [paOf, Finset.mem_filter] at hmem
    obtain ⟨-, hmem⟩ := hmem
    have hcast : Fin.castLE k.2.le (⟨i.val, hlt⟩ : Fin ↑k) = i := by
      rw [Fin.castLE_mk]
    rwa [hcast] at hmem
  · intro hmem
    have hlt : i.val < k.val := by
      have h2 := he _ _ hmem
      simpa [Equiv.apply_symm_apply] using h2
    refine ⟨hlt, ?_⟩
    rw [hpa]
    simp only [paOf, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcast : Fin.castLE k.2.le (⟨i.val, hlt⟩ : Fin ↑k) = i := by
      rw [Fin.castLE_mk]
    rwa [hcast]

/-! ### T5-T7: covered reversals and the (<=) direction on structures -/

/-- A covered reversal of an acyclic structure is acyclic. -/
theorem IsAcyclic.coveredReversal {V : Type*} [DecidableEq V] {Pa Pa' : V → Finset V}
    (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa') : IsAcyclic Pa' := by
  obtain ⟨x, y, hxy, hPay, rfl⟩ := hc
  have hxx : x ∉ Pa x := fun hx => h x (Relation.TransGen.single hx)
  have hmem : ∀ u v : V,
      u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) v ↔
        ((u = y ∧ v = x) ∨ (¬(u = x ∧ v = y) ∧ u ∈ Pa v)) := by
    intro u v
    by_cases hvx : v = x
    · rw [hvx, Function.update_self, Finset.mem_insert]
      constructor
      · rintro (heq | h)
        · exact Or.inl ⟨heq, rfl⟩
        · exact Or.inr ⟨fun hcon => hxy hcon.2, h⟩
      · rintro (⟨heq, -⟩ | ⟨-, h⟩)
        · exact Or.inl heq
        · exact Or.inr h
    · by_cases hvy : v = y
      · rw [hvy, Function.update_of_ne (Ne.symm hxy), Function.update_self, hPay,
          Finset.mem_insert]
        constructor
        · intro h
          refine Or.inr ⟨?_, Or.inr h⟩
          rintro ⟨heq, -⟩
          rw [heq] at h
          exact hxx h
        · rintro (hjump | ⟨hne, (heq | h)⟩)
          · exact (hxy hjump.2.symm).elim
          · exact (hne ⟨heq, rfl⟩).elim
          · exact h
      · rw [Function.update_of_ne hvx, Function.update_of_ne hvy]
        constructor
        · intro h
          exact Or.inr ⟨fun hcon => hvy hcon.2, h⟩
        · rintro (⟨-, hcon⟩ | ⟨-, h⟩)
          · exact absurd hcon hvx
          · exact h
  have hno : ∀ a b, Relation.TransGen
      (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
      a b →
      (a = x → b ≠ y) ∧
        (Relation.ReflTransGen (fun u w => u ∈ Pa w) a b ∨
          (Relation.ReflTransGen (fun u w => u ∈ Pa w) a y ∧
            Relation.ReflTransGen (fun u w => u ∈ Pa w) x b)) := by
    intro a b hab
    refine Relation.TransGen.rec
      (motive := fun b _ => (a = x → b ≠ y) ∧
        (Relation.ReflTransGen (fun u w => u ∈ Pa w) a b ∨
          (Relation.ReflTransGen (fun u w => u ∈ Pa w) a y ∧
            Relation.ReflTransGen (fun u w => u ∈ Pa w) x b))) ?_ ?_ hab
    · intro b' s
      by_cases hj : a = y ∧ b' = x
      · rcases hj with ⟨ha, hb⟩
        refine ⟨?_, Or.inr ?_⟩
        · intro ha' hb'
          exact hxy (ha'.symm.trans ha)
        · rw [ha, hb]
          exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · obtain ⟨hnxy, hab'⟩ := ((hmem a b').mp s).resolve_left hj
        refine ⟨?_, Or.inl (Relation.ReflTransGen.single hab')⟩
        intro ha hb
        exact hnxy ⟨ha, hb⟩
    · intro b' c' h1 s ih
      have hs := (hmem _ _).mp s
      refine ⟨?_, ?_⟩
      · intro ha hb
        rw [hb] at hs
        rcases hs with (⟨-, hjyx⟩ | ⟨hn, hmy⟩)
        · exact hxy hjyx.symm
        · rw [hPay, Finset.mem_insert] at hmy
          rcases hmy with (heq | hmx)
          · exact (hn ⟨heq, rfl⟩).elim
          · have hxm : Relation.ReflTransGen (fun u w => u ∈ Pa w) x b' := by
              rcases ih.2 with h | ⟨-, h⟩
              · rw [ha] at h; exact h
              · exact h
            rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxm with (heq | htrans)
            · rw [heq] at hmx; exact h x (Relation.TransGen.single hmx)
            · exact h x (Relation.TransGen.tail htrans hmx)
      · rcases hs with (⟨hmy, hbx⟩ | ⟨-, hmb⟩)
        · rw [hbx]
          refine Or.inr ⟨?_, Relation.ReflTransGen.refl⟩
          rcases ih.2 with h | ⟨h, -⟩
          · rw [hmy] at h; exact h
          · exact h
        · rcases ih.2 with h | ⟨h1', h2'⟩
          · exact Or.inl (h.tail hmb)
          · exact Or.inr ⟨h1', h2'.tail hmb⟩
  have hT : ∀ a b, Relation.TransGen
      (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
      a b →
      Relation.TransGen (fun u w => u ∈ Pa w) a b ∨
        (Relation.ReflTransGen
          (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
          a y ∧
          Relation.ReflTransGen
            (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
            x b) := by
    intro a b hab
    refine Relation.TransGen.rec
      (motive := fun b _ => Relation.TransGen (fun u w => u ∈ Pa w) a b ∨
        (Relation.ReflTransGen
          (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
          a y ∧
          Relation.ReflTransGen
            (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
            x b)) ?_ ?_ hab
    · intro b' s
      by_cases hj : a = y ∧ b' = x
      · rcases hj with ⟨ha, hb⟩
        rw [ha, hb]
        exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · obtain ⟨-, hab'⟩ := ((hmem a b').mp s).resolve_left hj
        exact Or.inl (Relation.TransGen.single hab')
    · intro b' c' h1 s ih
      have hs := (hmem _ _).mp s
      rcases hs with (⟨hmy, hbx⟩ | ⟨-, hmb⟩)
      · rw [hbx]
        rw [hmy] at h1
        exact Or.inr ⟨h1.to_reflTransGen, Relation.ReflTransGen.refl⟩
      · rcases ih with h | ⟨h1', h2'⟩
        · exact Or.inl (h.tail hmb)
        · exact Or.inr ⟨h1', h2'.tail s⟩
  intro v hv
  rcases hT v v hv with hcycle | ⟨hvy, hxv⟩
  · exact h v hcycle
  · have hxy1 := hxv.trans hvy
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy1 with (heq | htrans)
    · exact hxy heq.symm
    · have hQ := hno x y htrans
      exact hQ.1 rfl rfl

/-! ### C1 edge helpers: the parent sets after a covered reversal -/

/-- Off the covered edge, `Pa'` agrees with `Pa`. -/
private theorem pa'_of_coveredReversal_ne {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {w : V} (hwx : w ≠ x) (hwy : w ≠ y) : Pa' w = Pa w := by
  rw [hPa', Function.update_of_ne hwx, Function.update_of_ne hwy]

/-- After the reversal, `y` has the parents `x` used to have. -/
private theorem pa'_of_coveredReversal_y {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) :
    Pa' y = Pa x := by
  rw [hPa', Function.update_of_ne (Ne.symm hxy), Function.update_self]

/-- After the reversal, `x` gains `y` as a parent and keeps its old parents. -/
private theorem pa'_of_coveredReversal_x {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) :
    Pa' x = insert y (Pa x) := by
  rw [hPa', Function.update_self]

/-- Membership version of `pa'_of_coveredReversal_ne`. -/
private theorem mem_pa'_of_coveredReversal_ne {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {u w : V} (hwx : w ≠ x) (hwy : w ≠ y) : u ∈ Pa' w ↔ u ∈ Pa w := by
  rw [pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' hwx hwy]

/-- Membership version of `pa'_of_coveredReversal_y`. -/
private theorem mem_pa'_of_coveredReversal_y {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {u : V} : u ∈ Pa' y ↔ u ∈ Pa x := by
  rw [pa'_of_coveredReversal_y h hc x y hxy hPay hPa']

/-- Membership version of `pa'_of_coveredReversal_x`. -/
private theorem mem_pa'_of_coveredReversal_x {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {u : V} : u ∈ Pa' x ↔ u = y ∨ u ∈ Pa x := by
  rw [pa'_of_coveredReversal_x h hc x y hxy hPay hPa', Finset.mem_insert]

/-- Descendants of a node off the covered edge agree before and after the reversal. -/
private theorem isDescendantPa_iff_of_coveredReversal_off {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {w d : V} (hwx : w ≠ x) (hwy : w ≠ y) :
    IsDescendantPa Pa' w d ↔ IsDescendantPa Pa w d := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  have eNe : ∀ {u v : V}, v ≠ x → v ≠ y → (u ∈ Pa' v ↔ u ∈ Pa v) :=
    fun h1 h2 => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' h1 h2
  have eY : ∀ {u : V}, u ∈ Pa' y ↔ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  have eX : ∀ {u : V}, u ∈ Pa' x ↔ u = y ∨ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa'
  constructor
  · intro hpd
    have key : ∀ {d : V},
        Relation.ReflTransGen (fun u v => u ∈ Pa' v) w d →
          Relation.ReflTransGen (fun u v => u ∈ Pa v) w d ∧
            (d = y → Relation.ReflTransGen (fun u v => u ∈ Pa v) w x) := by
      intro d h'
      refine Relation.ReflTransGen.rec (motive := fun d _ =>
        Relation.ReflTransGen (fun u v => u ∈ Pa v) w d ∧
          (d = y → Relation.ReflTransGen (fun u v => u ∈ Pa v) w x)) ?_ ?_ h'
      · exact ⟨Relation.ReflTransGen.refl, fun hcon => absurd hcon hwy⟩
      · intro b c h1 h2 ih
        constructor
        · by_cases hcx : c = x
          · subst hcx
            rw [eX] at h2
            rcases h2 with rfl | hmx
            · exact ih.2 rfl
            · exact ih.1.tail hmx
          · by_cases hcy : c = y
            · subst hcy
              rw [eY] at h2
              exact (ih.1.tail h2).tail hxyPa
            · rw [eNe hcx hcy] at h2
              exact ih.1.tail h2
        · intro hcy
          subst hcy
          rw [eY] at h2
          exact ih.1.tail h2
    exact (key hpd).1
  · intro hpd
    have key : ∀ {d : V},
        Relation.ReflTransGen (fun u v => u ∈ Pa v) w d →
          Relation.ReflTransGen (fun u v => u ∈ Pa' v) w d ∧
            (d = x → Relation.ReflTransGen (fun u v => u ∈ Pa' v) w y) := by
      intro d h'
      refine Relation.ReflTransGen.rec (motive := fun d _ =>
        Relation.ReflTransGen (fun u v => u ∈ Pa' v) w d ∧
          (d = x → Relation.ReflTransGen (fun u v => u ∈ Pa' v) w y)) ?_ ?_ h'
      · exact ⟨Relation.ReflTransGen.refl, fun hcon => absurd hcon hwx⟩
      · intro b c h1 h2 ih
        constructor
        · by_cases hcase : b = x ∧ c = y
          · rcases hcase with ⟨rfl, rfl⟩
            exact ih.2 rfl
          · have h2' : b ∈ Pa' c := by
              by_cases hcx : c = x
              · subst hcx
                rw [eX]
                exact Or.inr h2
              · by_cases hcy : c = y
                · subst hcy
                  have hbx : b ≠ x := fun hcon => hcase ⟨hcon, rfl⟩
                  rw [eY]
                  rw [hPay, Finset.mem_insert] at h2
                  rcases h2 with rfl | hmx
                  · exact absurd rfl hbx
                  · exact hmx
                · rw [eNe hcx hcy]
                  exact h2
            exact ih.1.tail h2'
        · intro hcx
          subst hcx
          have hby : b ∈ Pa' y := eY.mpr h2
          exact ih.1.tail hby
    exact (key hpd).1

/-- After the reversal, the descendants of `y` are the old descendants of `x`. -/
private theorem isDescendantPa_y_iff_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {d : V} : IsDescendantPa Pa' y d ↔ IsDescendantPa Pa x d := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  have hyPa' : y ∈ Pa' x := by
    rw [pa'_of_coveredReversal_x h hc x y hxy hPay hPa']
    exact Finset.mem_insert_self y (Pa x)
  have eNe : ∀ {u v : V}, v ≠ x → v ≠ y → (u ∈ Pa' v ↔ u ∈ Pa v) :=
    fun h1 h2 => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' h1 h2
  have eY : ∀ {u : V}, u ∈ Pa' y ↔ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  have eX : ∀ {u : V}, u ∈ Pa' x ↔ u = y ∨ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa'
  constructor
  · intro hpd
    have key : ∀ {d : V}, Relation.ReflTransGen (fun u v => u ∈ Pa' v) y d →
        Relation.ReflTransGen (fun u v => u ∈ Pa v) x d := by
      intro d h'
      refine Relation.ReflTransGen.rec (motive := fun d _ =>
        Relation.ReflTransGen (fun u v => u ∈ Pa v) x d) ?_ ?_ h'
      · exact Relation.ReflTransGen.single hxyPa
      · intro b c h1 h2 ih
        by_cases hcx : c = x
        · subst hcx
          exact Relation.ReflTransGen.refl
        · by_cases hcy : c = y
          · subst hcy
            exact Relation.ReflTransGen.single hxyPa
          · rw [eNe hcx hcy] at h2
            exact ih.tail h2
    exact key hpd
  · intro hpd
    have key : ∀ {d : V}, Relation.ReflTransGen (fun u v => u ∈ Pa v) x d →
        Relation.ReflTransGen (fun u v => u ∈ Pa' v) y d := by
      intro d h'
      refine Relation.ReflTransGen.rec (motive := fun d _ =>
        Relation.ReflTransGen (fun u v => u ∈ Pa' v) y d) ?_ ?_ h'
      · exact Relation.ReflTransGen.single hyPa'
      · intro b c h1 h2 ih
        by_cases hcase : b = x ∧ c = y
        · rcases hcase with ⟨rfl, rfl⟩
          exact Relation.ReflTransGen.refl
        · have h2' : b ∈ Pa' c := by
            by_cases hcx : c = x
            · subst hcx
              rw [eX]
              exact Or.inr h2
            · by_cases hcy : c = y
              · subst hcy
                have hbx : b ≠ x := fun hcon => hcase ⟨hcon, rfl⟩
                rw [eY]
                rw [hPay, Finset.mem_insert] at h2
                rcases h2 with rfl | hmx
                · exact absurd rfl hbx
                · exact hmx
              · rw [eNe hcx hcy]
                exact h2
          exact ih.tail h2'
    exact key hpd

/-- Every old descendant of `y` stays a descendant of `y` after the reversal. -/
private theorem isDescendantPa_y_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {d : V} : IsDescendantPa Pa y d → IsDescendantPa Pa' y d := by
  intro hpd
  have eNe : ∀ {u v : V}, v ≠ x → v ≠ y → (u ∈ Pa' v ↔ u ∈ Pa v) :=
    fun h1 h2 => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' h1 h2
  have eY : ∀ {u : V}, u ∈ Pa' y ↔ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  have eX : ∀ {u : V}, u ∈ Pa' x ↔ u = y ∨ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa'
  have key : ∀ {d : V}, Relation.ReflTransGen (fun u v => u ∈ Pa v) y d →
      Relation.ReflTransGen (fun u v => u ∈ Pa' v) y d := by
    intro d h'
    refine Relation.ReflTransGen.rec (motive := fun d _ =>
      Relation.ReflTransGen (fun u v => u ∈ Pa' v) y d) ?_ ?_ h'
    · exact Relation.ReflTransGen.refl
    · intro b c h1 h2 ih
      by_cases hcase : b = x ∧ c = y
      · rcases hcase with ⟨rfl, rfl⟩
        exact Relation.ReflTransGen.refl
      · have h2' : b ∈ Pa' c := by
          by_cases hcx : c = x
          · subst hcx
            rw [eX]
            exact Or.inr h2
          · by_cases hcy : c = y
            · subst hcy
              have hbx : b ≠ x := fun hcon => hcase ⟨hcon, rfl⟩
              rw [eY]
              rw [hPay, Finset.mem_insert] at h2
              rcases h2 with rfl | hmx
              · exact absurd rfl hbx
              · exact hmx
            · rw [eNe hcx hcy]
              exact h2
        exact ih.tail h2'
  exact key hpd

/-- A covered reversal is symmetric as data: `Pa` is a covered reversal of `Pa'`. -/
private theorem coveredReversal_symm_data {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) :
    CoveredReversal Pa' Pa := by
  have eY : Pa' y = Pa x := pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  have eX : Pa' x = insert y (Pa x) :=
    pa'_of_coveredReversal_x h hc x y hxy hPay hPa'
  refine ⟨y, x, Ne.symm hxy, ?_, ?_⟩
  · rw [eX, eY]
  · funext w
    by_cases hwx : w = x
    · subst hwx
      rw [Function.update_of_ne hxy, Function.update_self, eY]
    · by_cases hwy : w = y
      · subst hwy
        rw [Function.update_self, eY, hPay]
      · rw [Function.update_of_ne hwy, Function.update_of_ne hwx,
          pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' hwx hwy]

/-- A covered reversal preserves adjacency. -/
private theorem adjacent_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {u w : V} : Adjacent Pa' u w ↔ Adjacent Pa u w := by
  have hxx : x ∉ Pa x := fun hx => h x (Relation.TransGen.single hx)
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  have eNe : ∀ {u v : V}, v ≠ x → v ≠ y → (u ∈ Pa' v ↔ u ∈ Pa v) :=
    fun h1 h2 => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' h1 h2
  have eY : ∀ {u : V}, u ∈ Pa' y ↔ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  have eX : ∀ {u : V}, u ∈ Pa' x ↔ u = y ∨ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa'
  have key : ∀ {u w : V},
      u ∈ Pa' w ↔ (u = y ∧ w = x) ∨ (u ∈ Pa w ∧ ¬(u = x ∧ w = y)) := by
    intro u w
    by_cases hwx : w = x
    · subst hwx
      rw [eX]
      constructor
      · rintro (hu | h)
        · exact Or.inl ⟨hu, rfl⟩
        · exact Or.inr ⟨h, fun hcon => hxy hcon.2⟩
      · rintro (⟨hu, -⟩ | ⟨h, -⟩)
        · exact Or.inl hu
        · exact Or.inr h
    · by_cases hwy : w = y
      · subst hwy
        rw [eY, hPay, Finset.mem_insert]
        constructor
        · intro h
          refine Or.inr ⟨Or.inr h, ?_⟩
          rintro ⟨hu, -⟩
          rw [hu] at h
          exact hxx h
        · rintro (⟨-, h2⟩ | ⟨h, hne⟩)
          · exact absurd h2.symm hxy
          · rcases h with hu | h
            · exact absurd ⟨hu, rfl⟩ hne
            · exact h
      · rw [eNe hwx hwy]
        constructor
        · intro h
          exact Or.inr ⟨h, fun hcon => hwy hcon.2⟩
        · rintro (⟨-, hcon⟩ | ⟨h, -⟩)
          · exact absurd hcon hwx
          · exact h
  unfold Adjacent
  rw [key, key]
  constructor
  · rintro ((⟨hu, hw⟩ | ⟨h, -⟩) | (⟨hw, hu⟩ | ⟨h, -⟩))
    · rw [hu, hw]; exact Or.inr hxyPa
    · exact Or.inl h
    · rw [hu, hw]; exact Or.inl hxyPa
    · exact Or.inr h
  · rintro (h | h)
    · by_cases hcon : u = x ∧ w = y
      · obtain ⟨hu, hw⟩ := hcon
        rw [hu, hw]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨h, hcon⟩)
    · by_cases hcon : w = x ∧ u = y
      · obtain ⟨hw, hu⟩ := hcon
        rw [hw, hu]
        exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨h, hcon⟩)

/-- A covered reversal preserves skeleton paths. -/
private theorem isPathPa_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {a b : V} {p : List V} : IsPathPa Pa' a b p ↔ IsPathPa Pa a b p := by
  have hadj : ∀ u w, Adjacent Pa' u w ↔ Adjacent Pa u w :=
    fun u w => adjacent_of_coveredReversal h hc x y hxy hPay hPa'
  unfold IsPathPa
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2.imp (fun u w => (hadj u w).mp), h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2.imp (fun u w => (hadj u w).mpr), h3, h4⟩

/-- Off the covered edge, the blocked-at status of a triple agrees. -/
private theorem blockedAtPa_of_coveredReversal_ne {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {u m w : V} (hmx : m ≠ x) (hmy : m ≠ y) :
    BlockedAtPa Pa' Z u m w ↔ BlockedAtPa Pa Z u m w := by
  have e1 : u ∈ Pa' m ↔ u ∈ Pa m :=
    mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' hmx hmy
  have e2 : w ∈ Pa' m ↔ w ∈ Pa m :=
    mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' hmx hmy
  have e3 : ∀ d, IsDescendantPa Pa' m d ↔ IsDescendantPa Pa m d :=
    fun d => isDescendantPa_iff_of_coveredReversal_off h hc x y hxy hPay hPa' hmx hmy
  unfold BlockedAtPa
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨e1.mp h1, e2.mp h2, fun d hd => h3 d ((e3 d).mpr hd)⟩
    · exact Or.inr ⟨fun hcon => h1 ⟨e1.mpr hcon.1, e2.mpr hcon.2⟩, h2⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨e1.mpr h1, e2.mpr h2, fun d hd => h3 d ((e3 d).mp hd)⟩
    · exact Or.inr ⟨fun hcon => h1 ⟨e1.mp hcon.1, e2.mp hcon.2⟩, h2⟩

/-- Descendants of `x` after the reversal: `x` itself and the old descendants of the old
non-`y` children of `x`. (A `Pa`-path starting with the covered edge `x → y` has no `Pa'`
counterpart, so there is no plain `Pa'`/`Pa` iff for `x`.) -/
private theorem isDescendantPa_x_iff_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {d : V} : IsDescendantPa Pa' x d ↔
      d = x ∨ ∃ v, v ≠ x ∧ v ≠ y ∧ x ∈ Pa v ∧ IsDescendantPa Pa v d := by
  have hxx : x ∉ Pa x := fun hx => h x (Relation.TransGen.single hx)
  have eNe : ∀ {u v : V}, v ≠ x → v ≠ y → (u ∈ Pa' v ↔ u ∈ Pa v) :=
    fun h1 h2 => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa' h1 h2
  have eY : ∀ {u : V}, u ∈ Pa' y ↔ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  constructor
  · intro hpd
    have key : ∀ {d : V}, Relation.ReflTransGen (fun u v => u ∈ Pa' v) x d →
        d = x ∨ ∃ v, v ≠ x ∧ v ≠ y ∧ x ∈ Pa v ∧
          Relation.ReflTransGen (fun u v => u ∈ Pa v) v d := by
      intro d h'
      refine Relation.ReflTransGen.rec (motive := fun d _ =>
        d = x ∨ ∃ v, v ≠ x ∧ v ≠ y ∧ x ∈ Pa v ∧
          Relation.ReflTransGen (fun u v => u ∈ Pa v) v d) ?_ ?_ h'
      · exact Or.inl rfl
      · intro b c h1 h2 ih
        by_cases hcx : c = x
        · exact Or.inl hcx
        · rcases ih with hbx | ⟨v, hvnx, hvny, hxv, hvd⟩
          · rw [hbx] at h2
            by_cases hcy : c = y
            · rw [hcy] at h2
              rw [eY] at h2
              exact absurd h2 hxx
            · rw [eNe hcx hcy] at h2
              exact Or.inr ⟨c, hcx, hcy, h2, Relation.ReflTransGen.refl⟩
          · by_cases hcy : c = y
            · rw [hcy] at h2
              rw [eY] at h2
              have hrx : Relation.ReflTransGen (fun u v => u ∈ Pa v) v x :=
                hvd.tail h2
              rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrx with heq | htrans
              · rw [heq] at hxv
                exact (h v (Relation.TransGen.single hxv)).elim
              · exact (h v (htrans.tail hxv)).elim
            · rw [eNe hcx hcy] at h2
              exact Or.inr ⟨v, hvnx, hvny, hxv, hvd.tail h2⟩
    exact key hpd
  · rintro (hdx | ⟨v, hvnx, hvny, hxv, hvd⟩)
    · subst hdx
      exact Relation.ReflTransGen.refl
    · have hxv' : x ∈ Pa' v := (eNe hvnx hvny).mpr hxv
      have hvd' : Relation.ReflTransGen (fun u v => u ∈ Pa' v) v d :=
        (isDescendantPa_iff_of_coveredReversal_off h hc x y hxy hPay hPa' hvnx hvny).mpr hvd
      exact (Relation.ReflTransGen.single hxv').trans hvd'

/-- An infix triple occurs at some index. -/
private theorem infix_triple_getElem {V : Type*} {p : List V} {x y w : V}
    (hinfix : List.IsInfix [x, y, w] p) :
    ∃ (i : ℕ) (_ : i + 2 < p.length), p[i] = x ∧ p[i + 1] = y ∧ p[i + 2] = w := by
  obtain ⟨s, t, hst⟩ := hinfix
  subst hst
  have h3 : ([x, y, w] : List V).length = 3 := rfl
  have hlen : s.length + 2 < (s ++ [x, y, w] ++ t).length := by
    rw [List.length_append, List.length_append, h3]
    omega
  have hlen2 : (s ++ [x, y, w]).length = s.length + 3 := by
    rw [List.length_append, h3]
  refine ⟨s.length, hlen, ?_, ?_, ?_⟩
  · rw [List.getElem_append_left (by omega : s.length < (s ++ [x, y, w]).length),
      List.getElem_append_right (by omega : s.length ≤ s.length)]
    simp only [Nat.sub_self]
    rfl
  · rw [List.getElem_append_left (by omega : s.length + 1 < (s ++ [x, y, w]).length),
      List.getElem_append_right (by omega : s.length ≤ s.length + 1)]
    simp only [show s.length + 1 - s.length = 1 by omega]
    rfl
  · rw [List.getElem_append_left (by omega : s.length + 2 < (s ++ [x, y, w]).length),
      List.getElem_append_right (by omega : s.length ≤ s.length + 2)]
    simp only [show s.length + 2 - s.length = 2 by omega]
    rfl

/-- A path is blocked iff some infix triple of it is. -/
private theorem pathBlockedPa_iff {V : Type*} (Pa : V → Finset V) (Z : Set V) (p : List V) :
    PathBlockedPa Pa Z p ↔
      ∃ u m w, List.IsInfix [u, m, w] p ∧ BlockedAtPa Pa Z u m w := by
  constructor
  · rintro ⟨i, hi, hb⟩
    refine ⟨p[i], p[i + 1], p[i + 2], ?_, hb⟩
    refine ⟨p.take i, p.drop (i + 3), ?_⟩
    have h0 : i < p.length := by omega
    have h1 : i + 1 < p.length := by omega
    have e0 : p.drop i = p[i] :: p.drop (i + 1) := List.drop_eq_getElem_cons h0
    have e1 : p.drop (i + 1) = p[i + 1] :: p.drop (i + 2) := List.drop_eq_getElem_cons h1
    have e2 : p.drop (i + 2) = p[i + 2] :: p.drop (i + 3) := List.drop_eq_getElem_cons hi
    have hp := List.take_append_drop i p
    rw [e0, e1, e2] at hp
    have hlit : [p[i], p[i + 1], p[i + 2]] ++ p.drop (i + 3) =
        p[i] :: p[i + 1] :: p[i + 2] :: p.drop (i + 3) := rfl
    rw [List.append_assoc, hlit]
    exact hp
  · rintro ⟨u, m, w, hinfix, hb⟩
    obtain ⟨i, hi, e0, e1, e2⟩ := infix_triple_getElem hinfix
    refine ⟨i, hi, ?_⟩
    rwa [e0, e1, e2]

/-- Removing one interior node across a shortcut keeps a path a path. -/
private theorem isPathPa_eraseIdx {V : Type*} (Pa : V → Finset V) {a b : V} {p : List V} {i : ℕ}
    (hpath : IsPathPa Pa a b p) (hi : i + 2 < p.length)
    (hadj : Adjacent Pa p[i] p[i + 2]) :
    IsPathPa Pa a b (p.eraseIdx (i + 1)) := by
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hpath
  have hi1 : i + 1 < p.length := by omega
  have hqlen : (p.eraseIdx (i + 1)).length = p.length - 1 :=
    List.length_eraseIdx_of_lt hi1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.Nodup.eraseIdx _ hnodup
  · rw [List.isChain_iff_getElem]
    intro j hj
    by_cases hji : j + 1 < i + 1
    · have e1 := List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := j)
        (by omega) (by omega)
      have e2 := List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := j + 1)
        (by omega) (by omega)
      rw [e1, e2]
      exact List.IsChain.getElem hchain j (by omega)
    · replace hji := not_lt.mp hji
      by_cases hjeq : j = i
      · subst hjeq
        have e1 := List.getElem_eraseIdx_of_lt (l := p) (i := j + 1) (j := j)
          (by omega) (by omega)
        have e2 := List.getElem_eraseIdx_of_ge (l := p) (i := j + 1) (j := j + 1)
          (by omega) (by omega)
        rw [e1, e2]
        exact hadj
      · have e1 := List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := j)
          (by omega) (by omega)
        have e2 := List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := j + 1)
          (by omega) (by omega)
        rw [e1, e2]
        exact List.IsChain.getElem hchain (j + 1) (by omega)
  · have hq : p.eraseIdx (i + 1) = p.take (i + 1) ++ p.drop (i + 1 + 1) :=
      List.eraseIdx_eq_take_drop_succ p (i + 1)
    rw [hq, List.head?_append, List.head?_take]
    simp only [show i + 1 ≠ 0 by omega]
    rw [hhead]
    rfl
  · have hlast' : p[p.length - 1]? = some b := by
      rw [← List.getLast?_eq_getElem?]
      exact hlast
    rw [List.getLast?_eq_getElem?, hqlen]
    have h1 : p.length - 1 - 1 < (p.eraseIdx (i + 1)).length := by omega
    rw [List.getElem?_eq_getElem h1]
    have e := List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := p.length - 1 - 1)
      h1 (by omega)
    rw [e]
    simp only [show p.length - 1 - 1 + 1 = p.length - 1 by omega]
    have h2 : p.length - 1 < p.length := by omega
    have hsome := List.getElem?_eq_getElem (l := p) (i := p.length - 1) h2
    exact hsome.symm.trans hlast'

/-- Every triple of the spliced list is an old triple or a splice triple. -/
private theorem eraseIdx_triple_transfer {V : Type*} (p : List V) (i : ℕ)
    (hi : i + 2 < p.length) (j : ℕ) (hj : j + 2 < (p.eraseIdx (i + 1)).length) :
    (∃ (k : ℕ) (_ : k + 2 < p.length), (p.eraseIdx (i + 1))[j] = p[k] ∧
      (p.eraseIdx (i + 1))[j + 1] = p[k + 1] ∧ (p.eraseIdx (i + 1))[j + 2] = p[k + 2])
    ∨ (j + 1 = i ∧ ∃ (_ : j + 2 < p.length), (p.eraseIdx (i + 1))[j] = p[j] ∧
      (p.eraseIdx (i + 1))[j + 1] = p[i] ∧ (p.eraseIdx (i + 1))[j + 2] = p[i + 2])
    ∨ (j = i ∧ ∃ (_ : i + 3 < p.length), (p.eraseIdx (i + 1))[j] = p[i] ∧
      (p.eraseIdx (i + 1))[j + 1] = p[i + 2] ∧
      (p.eraseIdx (i + 1))[j + 2] = p[i + 3]) := by
  have hqlen : (p.eraseIdx (i + 1)).length = p.length - 1 :=
    List.length_eraseIdx_of_lt (by omega)
  have hj' : j + 2 < p.length - 1 := by omega
  by_cases h1 : j + 1 < i + 1
  · by_cases h2 : j + 1 = i
    · right; left
      refine ⟨h2, by omega, ?_, ?_, ?_⟩
      · exact List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := j)
          (by omega) (by omega)
      · simp only [h2]
        exact List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := i)
          (by omega) (by omega)
      · simp only [show j + 2 = i + 1 by omega]
        exact List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := i + 1)
          (by omega) (by omega)
    · left
      refine ⟨j, by omega, ?_, ?_, ?_⟩
      · exact List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := j)
          (by omega) (by omega)
      · exact List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := j + 1)
          (by omega) (by omega)
      · exact List.getElem_eraseIdx_of_lt (l := p) (i := i + 1) (j := j + 2)
          (by omega) (by omega)
  · replace h1 := not_lt.mp h1
    by_cases h2 : j = i
    · subst h2
      right; right
      refine ⟨rfl, by omega, ?_, ?_, ?_⟩
      · exact List.getElem_eraseIdx_of_lt (l := p) (i := j + 1) (j := j)
          (by omega) (by omega)
      · exact List.getElem_eraseIdx_of_ge (l := p) (i := j + 1) (j := j + 1)
          (by omega) (by omega)
      · exact List.getElem_eraseIdx_of_ge (l := p) (i := j + 1) (j := j + 2)
          (by omega) (by omega)
    · left
      refine ⟨j + 1, by omega, ?_, ?_, ?_⟩
      · exact List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := j)
          (by omega) (by omega)
      · exact List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := j + 1)
          (by omega) (by omega)
      · exact List.getElem_eraseIdx_of_ge (l := p) (i := i + 1) (j := j + 2)
          (by omega) (by omega)

/-- An unblocked path through a covered `x, y` with a shortcut `x ~ w` shortens. -/
private theorem exists_shorter_unblocked_of_x_y_w {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b w : V} {p : List V}
    (hpath : IsPathPa Pa a b p) (hunblocked : ¬ PathBlockedPa Pa Z p)
    (hwx : w ∈ Pa x) (hyZ : y ∈ Z)
    (hinfix : List.IsInfix [x, y, w] p) :
    ∃ q, IsPathPa Pa a b q ∧ ¬ PathBlockedPa Pa Z q ∧ q.length < p.length := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  obtain ⟨i, hi, hix, hiy, hiw⟩ := infix_triple_getElem hinfix
  have hadj : Adjacent Pa p[i] p[i + 2] := by
    rw [hix, hiw]
    exact Or.inr hwx
  have hpathQ := isPathPa_eraseIdx Pa hpath hi hadj
  have hqlen : (p.eraseIdx (i + 1)).length < p.length := by
    rw [List.length_eraseIdx_of_lt (by omega : i + 1 < p.length)]
    omega
  refine ⟨p.eraseIdx (i + 1), hpathQ, ?_, hqlen⟩
  intro hblocked
  obtain ⟨j, hj, hb⟩ := hblocked
  obtain htrans := eraseIdx_triple_transfer p i hi j hj
  rcases htrans with ⟨k, hk, e0, e1, e2⟩ | ⟨hji, hj2lt, e0, e1, e2⟩ | ⟨hji, hi3, e0, e1, e2⟩
  · rw [e0, e1, e2] at hb
    exact hunblocked ⟨k, hk, hb⟩
  · have hji2 : j + 2 = i + 1 := by omega
    rw [e0, e1, e2, hix, hiw] at hb
    have hold : ¬ BlockedAtPa Pa Z p[j] x y := by
      have hcon : ¬ BlockedAtPa Pa Z p[j] p[j + 1] p[j + 2] :=
        fun h => hunblocked ⟨j, hj2lt, h⟩
      simp only [hji, hji2] at hcon
      rwa [hix, hiy] at hcon
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨-, -, hnocoll⟩ | ⟨-, hxZ⟩
    · exact hnocoll y (Relation.ReflTransGen.single hxyPa) hyZ
    · have hyx : y ∉ Pa x := by
        intro hyx
        exact h x ((Relation.TransGen.single hxyPa).tail hyx)
      have hnc : ¬ (p[j] ∈ Pa x ∧ y ∈ Pa x) := fun hcon => hyx hcon.2
      have hnb : ¬ (¬ (p[j] ∈ Pa x ∧ y ∈ Pa x) ∧ x ∈ Z) :=
        fun hcon => hold (Or.inr hcon)
      exact hnb ⟨hnc, hxZ⟩
  · rw [e0, e1, e2, hix, hiw] at hb
    have hold : ¬ BlockedAtPa Pa Z y w p[i + 3] := by
      have hcon : ¬ BlockedAtPa Pa Z p[i + 1] p[i + 2] p[i + 3] :=
        fun h => hunblocked ⟨i + 1, by omega, h⟩
      rwa [hiy, hiw] at hcon
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨-, -, hdesc⟩ | ⟨-, hwZ⟩
    · have hwy : IsDescendantPa Pa w y :=
        (Relation.ReflTransGen.single hwx).tail hxyPa
      exact hdesc y hwy hyZ
    · by_cases hcold : y ∈ Pa w ∧ p[i + 3] ∈ Pa w
      · obtain ⟨hyw, -⟩ := hcold
        exact h w (((Relation.TransGen.single hwx).tail hxyPa).tail hyw)
      · have hnb : ¬ (¬ (y ∈ Pa w ∧ p[i + 3] ∈ Pa w) ∧ w ∈ Z) :=
          fun hcon => hold (Or.inr hcon)
        exact hnb ⟨hcold, hwZ⟩

/-- An unblocked path through a covered `x, y` with a shortcut `u ~ x` shortens. -/
private theorem exists_shorter_unblocked_of_u_y_x {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b u : V} {p : List V}
    (hpath : IsPathPa Pa a b p) (hunblocked : ¬ PathBlockedPa Pa Z p)
    (hux : u ∈ Pa x) (hyZ : y ∈ Z)
    (hinfix : List.IsInfix [u, y, x] p) :
    ∃ q, IsPathPa Pa a b q ∧ ¬ PathBlockedPa Pa Z q ∧ q.length < p.length := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  obtain ⟨i, hi, hiu, hiy, hix⟩ := infix_triple_getElem hinfix
  have hadj : Adjacent Pa p[i] p[i + 2] := by
    rw [hiu, hix]
    exact Or.inl hux
  have hpathQ := isPathPa_eraseIdx Pa hpath hi hadj
  have hqlen : (p.eraseIdx (i + 1)).length < p.length := by
    rw [List.length_eraseIdx_of_lt (by omega : i + 1 < p.length)]
    omega
  refine ⟨p.eraseIdx (i + 1), hpathQ, ?_, hqlen⟩
  intro hblocked
  obtain ⟨j, hj, hb⟩ := hblocked
  obtain htrans := eraseIdx_triple_transfer p i hi j hj
  rcases htrans with ⟨k, hk, e0, e1, e2⟩ | ⟨hji, hj2lt, e0, e1, e2⟩ | ⟨hji, hi3, e0, e1, e2⟩
  · rw [e0, e1, e2] at hb
    exact hunblocked ⟨k, hk, hb⟩
  · have hji2 : j + 2 = i + 1 := by omega
    rw [e0, e1, e2, hiu, hix] at hb
    have hold : ¬ BlockedAtPa Pa Z p[j] u y := by
      have hcon : ¬ BlockedAtPa Pa Z p[j] p[j + 1] p[j + 2] :=
        fun h => hunblocked ⟨j, hj2lt, h⟩
      simp only [hji, hji2] at hcon
      rwa [hiu, hiy] at hcon
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨-, -, hdesc⟩ | ⟨-, huZ⟩
    · have hdy : IsDescendantPa Pa u y :=
        (Relation.ReflTransGen.single hux).tail hxyPa
      exact hdesc y hdy hyZ
    · by_cases hcold : p[j] ∈ Pa u ∧ y ∈ Pa u
      · obtain ⟨-, hyu⟩ := hcold
        exact h u (((Relation.TransGen.single hux).tail hxyPa).tail hyu)
      · have hnb : ¬ (¬ (p[j] ∈ Pa u ∧ y ∈ Pa u) ∧ u ∈ Z) :=
          fun hcon => hold (Or.inr hcon)
        exact hnb ⟨hcold, huZ⟩
  · rw [e0, e1, e2, hiu, hix] at hb
    have hold : ¬ BlockedAtPa Pa Z y x p[i + 3] := by
      have hcon : ¬ BlockedAtPa Pa Z p[i + 1] p[i + 2] p[i + 3] :=
        fun h => hunblocked ⟨i + 1, by omega, h⟩
      rwa [hiy, hix] at hcon
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨-, -, hnocoll⟩ | ⟨-, hxZ⟩
    · exact hnocoll y (Relation.ReflTransGen.single hxyPa) hyZ
    · have hyx : y ∉ Pa x := by
        intro hyx
        exact h x ((Relation.TransGen.single hxyPa).tail hyx)
      have hnc : ¬ (y ∈ Pa x ∧ p[i + 3] ∈ Pa x) := fun hcon => hyx hcon.1
      have hnb : ¬ (¬ (y ∈ Pa x ∧ p[i + 3] ∈ Pa x) ∧ x ∈ Z) :=
        fun hcon => hold (Or.inr hcon)
      exact hnb ⟨hnc, hxZ⟩

/-- The covered child `y` is not a parent of `x`. -/
private theorem y_not_mem_pa_x_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) :
    y ∉ Pa x := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  intro hyx
  exact h x ((Relation.TransGen.single hxyPa).tail hyx)

/-- Parents of `x` have neither `x` nor `y` as a parent. -/
private theorem not_mem_pa_of_mem_pa_x_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {u : V} (hux : u ∈ Pa x) : x ∉ Pa u ∧ y ∉ Pa u := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  constructor
  · intro hxu
    exact h x ((Relation.TransGen.single hxu).tail hux)
  · intro hyu
    exact h y (((Relation.TransGen.single hyu).tail hux).tail hxyPa)

/-- An unblocked path through a covered `x, y` with a shortcut `y ~ w` shortens. -/
private theorem exists_shorter_unblocked_of_y_x_w {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b w : V} {p : List V}
    (hpath : IsPathPa Pa a b p) (hunblocked : ¬ PathBlockedPa Pa Z p)
    (hwx : w ∈ Pa x)
    (hinfix : List.IsInfix [y, x, w] p) :
    ∃ q, IsPathPa Pa a b q ∧ ¬ PathBlockedPa Pa Z q ∧ q.length < p.length := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  have hwyPa : w ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_of_mem hwx
  obtain ⟨i, hi, hiy, hix, hiw⟩ := infix_triple_getElem hinfix
  have hadj : Adjacent Pa p[i] p[i + 2] := by
    rw [hiy, hiw]
    exact Or.inr hwyPa
  have hpathQ := isPathPa_eraseIdx Pa hpath hi hadj
  have hqlen : (p.eraseIdx (i + 1)).length < p.length := by
    rw [List.length_eraseIdx_of_lt (by omega : i + 1 < p.length)]
    omega
  refine ⟨p.eraseIdx (i + 1), hpathQ, ?_, hqlen⟩
  intro hblocked
  obtain ⟨j, hj, hb⟩ := hblocked
  obtain htrans := eraseIdx_triple_transfer p i hi j hj
  rcases htrans with ⟨k, hk, e0, e1, e2⟩ | ⟨hji, hj2lt, e0, e1, e2⟩ | ⟨hji, hi3, e0, e1, e2⟩
  · rw [e0, e1, e2] at hb
    exact hunblocked ⟨k, hk, hb⟩
  · have hji2 : j + 2 = i + 1 := by omega
    rw [e0, e1, e2, hiy, hiw] at hb
    have hold : ¬ BlockedAtPa Pa Z p[j] y x := by
      have hcon : ¬ BlockedAtPa Pa Z p[j] p[j + 1] p[j + 2] :=
        fun h => hunblocked ⟨j, hj2lt, h⟩
      simp only [hji, hji2] at hcon
      rwa [hiy, hix] at hcon
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨hpjy, -, hdesc⟩ | ⟨hnc, hyZ⟩
    · exact hold (Or.inl ⟨hpjy, hxyPa, hdesc⟩)
    · have hnc' : ¬ (p[j] ∈ Pa y ∧ x ∈ Pa y) :=
        fun hcon => hnc ⟨hcon.1, hwyPa⟩
      exact hold (Or.inr ⟨hnc', hyZ⟩)
  · rw [e0, e1, e2, hiy, hiw] at hb
    have hold : ¬ BlockedAtPa Pa Z x w p[i + 3] := by
      have hcon : ¬ BlockedAtPa Pa Z p[i + 1] p[i + 2] p[i + 3] :=
        fun h => hunblocked ⟨i + 1, by omega, h⟩
      rwa [hix, hiw] at hcon
    have hxw : x ∉ Pa w :=
      (not_mem_pa_of_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa' hwx).1
    have hyw : y ∉ Pa w :=
      (not_mem_pa_of_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa' hwx).2
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨hyw', -, -⟩ | ⟨-, hwZ⟩
    · exact hyw hyw'
    · have hnc : ¬ (x ∈ Pa w ∧ p[i + 3] ∈ Pa w) := fun hcon => hxw hcon.1
      exact hold (Or.inr ⟨hnc, hwZ⟩)

/-- An unblocked path through a covered `x, y` with a shortcut `u ~ y` shortens. -/
private theorem exists_shorter_unblocked_of_u_x_y {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b u : V} {p : List V}
    (hpath : IsPathPa Pa a b p) (hunblocked : ¬ PathBlockedPa Pa Z p)
    (hux : u ∈ Pa x)
    (hinfix : List.IsInfix [u, x, y] p) :
    ∃ q, IsPathPa Pa a b q ∧ ¬ PathBlockedPa Pa Z q ∧ q.length < p.length := by
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  have huyPa : u ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_of_mem hux
  obtain ⟨i, hi, hiu, hix, hiy⟩ := infix_triple_getElem hinfix
  have hadj : Adjacent Pa p[i] p[i + 2] := by
    rw [hiu, hiy]
    exact Or.inl huyPa
  have hpathQ := isPathPa_eraseIdx Pa hpath hi hadj
  have hqlen : (p.eraseIdx (i + 1)).length < p.length := by
    rw [List.length_eraseIdx_of_lt (by omega : i + 1 < p.length)]
    omega
  refine ⟨p.eraseIdx (i + 1), hpathQ, ?_, hqlen⟩
  intro hblocked
  obtain ⟨j, hj, hb⟩ := hblocked
  obtain htrans := eraseIdx_triple_transfer p i hi j hj
  rcases htrans with ⟨k, hk, e0, e1, e2⟩ | ⟨hji, hj2lt, e0, e1, e2⟩ | ⟨hji, hi3, e0, e1, e2⟩
  · rw [e0, e1, e2] at hb
    exact hunblocked ⟨k, hk, hb⟩
  · have hji2 : j + 2 = i + 1 := by omega
    rw [e0, e1, e2, hiu, hiy] at hb
    have hold : ¬ BlockedAtPa Pa Z p[j] u x := by
      have hcon : ¬ BlockedAtPa Pa Z p[j] p[j + 1] p[j + 2] :=
        fun h => hunblocked ⟨j, hj2lt, h⟩
      simp only [hji, hji2] at hcon
      rwa [hiu, hix] at hcon
    have hxu : x ∉ Pa u :=
      (not_mem_pa_of_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa' hux).1
    have hyu : y ∉ Pa u :=
      (not_mem_pa_of_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa' hux).2
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨-, hyu', -⟩ | ⟨-, huZ⟩
    · exact hyu hyu'
    · have hnc : ¬ (p[j] ∈ Pa u ∧ x ∈ Pa u) := fun hcon => hxu hcon.2
      exact hold (Or.inr ⟨hnc, huZ⟩)
  · rw [e0, e1, e2, hiu, hiy] at hb
    have hold : ¬ BlockedAtPa Pa Z x y p[i + 3] := by
      have hcon : ¬ BlockedAtPa Pa Z p[i + 1] p[i + 2] p[i + 3] :=
        fun h => hunblocked ⟨i + 1, by omega, h⟩
      rwa [hix, hiy] at hcon
    unfold BlockedAtPa at hb hold
    rcases hb with ⟨hu, hp3, hdesc⟩ | ⟨hnc, hyZ⟩
    · exact hold (Or.inl ⟨hxyPa, hp3, hdesc⟩)
    · have hnc' : ¬ (x ∈ Pa y ∧ p[i + 3] ∈ Pa y) :=
        fun hcon => hnc ⟨huyPa, hcon.2⟩
      exact hold (Or.inr ⟨hnc', hyZ⟩)

/-- Replacing the covered parent `x` by `y` turns an unblocked `Pa`-path through the interior
node `x` into an unblocked `Pa'`-path. -/
private theorem replace_x_with_y_unblocked {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b : V} {p : List V}
    (hpath : IsPathPa Pa a b p) (hunblocked : ¬ PathBlockedPa Pa Z p)
    {i : ℕ} (hi : i < p.length) (hxi : p[i] = x)
    (hi0 : i ≠ 0) (hilast : i + 1 < p.length)
    (hpre : p[i - 1] ∈ Pa x) (hsuc : p[i + 1] ∈ Pa x)
    (hy_not : y ∉ p)
    (hwit : ∃ d, d ∈ Z ∧ IsDescendantPa Pa y d)
    (hxZ : x ∉ Z) :
    IsPathPa Pa' a b (p.map (fun v => if v = x then y else v)) ∧
      ¬ PathBlockedPa Pa' Z (p.map (fun v => if v = x then y else v)) := by
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hpath
  obtain ⟨d, hdZ, hdesc⟩ := hwit
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  set f : V → V := fun v => if v = x then y else v with hf
  have hfx : f x = y := by simp [hf]
  have hfv : ∀ {v : V}, v ≠ x → f v = v := fun hv => by simp [hf, hv]
  have hlen : (p.map f).length = p.length := List.length_map f
  have eY : ∀ {u : V}, u ∈ Pa' y ↔ u ∈ Pa x :=
    fun {u} => mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa'
  constructor
  · unfold IsPathPa
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hinj_on : ∀ a ∈ p, ∀ b ∈ p, f a = f b → a = b := by
        intro a ha b hb hab
        by_cases hax : a = x
        · by_cases hbx : b = x
          · subst hax; subst hbx; rfl
          · subst hax
            rw [hfx, hfv hbx] at hab
            rw [← hab] at hb
            exact (hy_not hb).elim
        · by_cases hbx : b = x
          · subst hbx
            rw [hfx, hfv hax] at hab
            rw [hab] at ha
            exact (hy_not ha).elim
          · rw [hfv hax, hfv hbx] at hab
            exact hab
      exact hnodup.map_on hinj_on
    · rw [List.isChain_iff_getElem]
      intro j hj
      rw [hlen] at hj
      simp only [List.getElem_map]
      by_cases hjx : p[j] = x
      · by_cases hj1x : p[j + 1] = x
        · have hcon : j = j + 1 :=
            (hnodup.getElem_inj_iff).mp (hjx.trans hj1x.symm)
          omega
        · have hji : j = i := (hnodup.getElem_inj_iff).mp (hjx.trans hxi.symm)
          subst hji
          rw [hxi, hfx, hfv hj1x]
          exact Or.inr (eY.mpr hsuc)
      · by_cases hj1x : p[j + 1] = x
        · have hji1 : j + 1 = i :=
            (hnodup.getElem_inj_iff).mp (hj1x.trans hxi.symm)
          subst hji1
          simp only [Nat.add_sub_cancel] at hpre
          rw [hfv hjx, hj1x, hfx]
          exact Or.inl (eY.mpr hpre)
        · rw [hfv hjx, hfv hj1x]
          exact (adjacent_of_coveredReversal h hc x y hxy hPay hPa').mpr
            (List.IsChain.getElem hchain j hj)
    · have ha_ne_x : a ≠ x := by
        intro hax
        rw [hax] at hhead
        have h0 : 0 < p.length := by omega
        have e0 : p[0] = x := by
          have hh := hhead
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hh
          simpa using hh
        have h0i : (0 : ℕ) = i := (hnodup.getElem_inj_iff).mp (e0.trans hxi.symm)
        omega
      rw [List.head?_map, hhead, Option.map_some]
      rw [hfv ha_ne_x]
    · have hb_ne_x : b ≠ x := by
        intro hbx
        rw [hbx] at hlast
        have h1 : p.length - 1 < p.length := by
          have h0 : 0 < p.length := by omega
          omega
        have elast : p[p.length - 1] = x := by
          have hh := hlast
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem h1] at hh
          simpa using hh
        have hli : p.length - 1 = i :=
          (hnodup.getElem_inj_iff).mp (elast.trans hxi.symm)
        omega
      rw [List.getLast?_map, hlast, Option.map_some]
      rw [hfv hb_ne_x]
  · intro hblocked
    obtain ⟨j, hj, hb⟩ := hblocked
    rw [hlen] at hj
    simp only [List.getElem_map] at hb
    by_cases hmid : j + 1 = i
    · have hmid' : p[j + 1] = x := by simp only [hmid]; exact hxi
      have hj_ne : p[j] ≠ x := by
        intro hcon
        have hji : j = i := (hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm)
        omega
      have hj2_ne : p[j + 2] ≠ x := by
        intro hcon
        have hji2 : j + 2 = i := (hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm)
        omega
      have hjm : j = i - 1 := by omega
      have hleft : p[j] ∈ Pa x := by simp only [hjm]; exact hpre
      have hj2 : j + 2 = i + 1 := by omega
      have hright : p[j + 2] ∈ Pa x := by simp only [hj2]; exact hsuc
      rw [hfv hj_ne, hmid', hfx, hfv hj2_ne] at hb
      have hcoll1 : p[j] ∈ Pa' y := eY.mpr hleft
      have hcoll2 : p[j + 2] ∈ Pa' y := eY.mpr hright
      have hdesc' : IsDescendantPa Pa x d :=
        (Relation.ReflTransGen.single hxyPa).trans hdesc
      have hdescPa' : IsDescendantPa Pa' y d :=
        (isDescendantPa_y_iff_of_coveredReversal h hc x y hxy hPay hPa').mpr hdesc'
      unfold BlockedAtPa at hb
      rcases hb with ⟨-, -, hnowit⟩ | ⟨hnc, -⟩
      · exact hnowit d hdescPa' hdZ
      · exact hnc ⟨hcoll1, hcoll2⟩
    · have hmid_ne_x : p[j + 1] ≠ x := by
        intro hcon
        have hji1 : j + 1 = i := (hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm)
        exact hmid hji1
      have hmid_ne_y : p[j + 1] ≠ y := by
        intro hcon
        have hmem : p[j + 1] ∈ p := List.getElem_mem (by omega : j + 1 < p.length)
        rw [hcon] at hmem
        exact hy_not hmem
      by_cases hleft : j = i
      · have hleft' : p[j] = x := by simp only [hleft]; exact hxi
        have hj2_ne : p[j + 2] ≠ x := by
          intro hcon
          have hji2 : j + 2 = i := (hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm)
          omega
        have hsuc_eq : j + 1 = i + 1 := by omega
        have hsuc' : p[j + 1] ∈ Pa x := by simp only [hsuc_eq]; exact hsuc
        have eNe_succ : ∀ {u : V}, u ∈ Pa' p[j + 1] ↔ u ∈ Pa p[j + 1] :=
          fun {u} => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa'
            hmid_ne_x hmid_ne_y
        have hL1 : x ∉ Pa p[j + 1] ∧ y ∉ Pa p[j + 1] :=
          not_mem_pa_of_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa' hsuc'
        have hold : ¬ BlockedAtPa Pa Z x p[j + 1] p[j + 2] := by
          intro hcon
          simp only [← hleft'] at hcon
          exact hunblocked ⟨j, hj, hcon⟩
        rw [hleft', hfx, hfv hmid_ne_x, hfv hj2_ne] at hb
        have hyF : y ∈ Pa' p[j + 1] → False :=
          fun hcon => hL1.2 (eNe_succ.mp hcon)
        unfold BlockedAtPa at hb hold
        rcases hb with ⟨hy', -, -⟩ | ⟨-, hsZ⟩
        · exact hyF hy'
        · apply hold
          exact Or.inr ⟨fun hcon => hL1.1 hcon.1, hsZ⟩
      · by_cases hright : j + 2 = i
        · have hright' : p[j + 2] = x := by simp only [hright]; exact hxi
          have hj_ne : p[j] ≠ x := by
            intro hcon
            have hji : j = i := (hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm)
            omega
          have hmid_eq : j + 1 = i - 1 := by omega
          have hpre' : p[j + 1] ∈ Pa x := by simp only [hmid_eq]; exact hpre
          have eNe_pred : ∀ {u : V}, u ∈ Pa' p[j + 1] ↔ u ∈ Pa p[j + 1] :=
            fun {u} => mem_pa'_of_coveredReversal_ne h hc x y hxy hPay hPa'
              hmid_ne_x hmid_ne_y
          have hL1 : x ∉ Pa p[j + 1] ∧ y ∉ Pa p[j + 1] :=
            not_mem_pa_of_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa' hpre'
          have hold : ¬ BlockedAtPa Pa Z p[j] p[j + 1] x := by
            intro hcon
            simp only [← hright'] at hcon
            exact hunblocked ⟨j, hj, hcon⟩
          rw [hfv hj_ne, hfv hmid_ne_x, hright', hfx] at hb
          have hyF : y ∈ Pa' p[j + 1] → False :=
            fun hcon => hL1.2 (eNe_pred.mp hcon)
          unfold BlockedAtPa at hb hold
          rcases hb with ⟨-, hy', -⟩ | ⟨-, hsZ⟩
          · exact hyF hy'
          · apply hold
            exact Or.inr ⟨fun hcon => hL1.1 hcon.2, hsZ⟩
        · have hj_ne : p[j] ≠ x := by
            intro hcon
            exact hleft ((hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm))
          have hj2_ne : p[j + 2] ≠ x := by
            intro hcon
            exact hright ((hnodup.getElem_inj_iff).mp (hcon.trans hxi.symm))
          rw [hfv hj_ne, hfv hmid_ne_x, hfv hj2_ne] at hb
          have hb_old := (blockedAtPa_of_coveredReversal_ne h hc x y hxy hPay hPa'
            hmid_ne_x hmid_ne_y).mp hb
          exact hunblocked ⟨j, hj, hb_old⟩

/-- Length of a take/drop splice. -/
private theorem splice_length {V : Type*} (p : List V) (k₁ k₂ : ℕ)
    (hk₁ : k₁ ≤ p.length) :
    (p.take k₁ ++ p.drop k₂).length = k₁ + (p.length - k₂) := by
  rw [List.length_append, List.length_take, List.length_drop, min_eq_left hk₁]

/-- Reading a prefix element of a take/drop splice. -/
private theorem splice_getElem_of_lt {V : Type*} (p : List V) (k₁ k₂ r : ℕ)
    (hk₁ : k₁ ≤ p.length)
    (hr : r < (p.take k₁ ++ p.drop k₂).length) (hlt : r < k₁) :
    (p.take k₁ ++ p.drop k₂)[r] = p[r] := by
  have htake : (p.take k₁).length = k₁ := by
    rw [List.length_take, min_eq_left hk₁]
  rw [List.getElem_append_left (by omega : r < (p.take k₁).length)]
  exact List.getElem_take

/-- Reading a suffix element of a take/drop splice. -/
private theorem splice_getElem_of_ge {V : Type*} (p : List V) (k₁ k₂ r : ℕ)
    (hk₁ : k₁ ≤ p.length)
    (hr : r < (p.take k₁ ++ p.drop k₂).length) (hge : k₁ ≤ r)
    (hqlen : (p.take k₁ ++ p.drop k₂).length = k₁ + (p.length - k₂) :=
      splice_length p k₁ k₂ hk₁) :
    (p.take k₁ ++ p.drop k₂)[r] = p[k₂ + (r - k₁)] := by
  have htake : (p.take k₁).length = k₁ := by
    rw [List.length_take, min_eq_left hk₁]
  rw [List.getElem_append_right (by omega : (p.take k₁).length ≤ r)]
  simp only [htake]
  exact List.getElem_drop

/-- Splicing a path across a shortcut keeps it a path. -/
private theorem isPathPa_take_drop {V : Type*} (Pa : V → Finset V) {a b : V} {p : List V}
    {k₁ k₂ : ℕ} (hpath : IsPathPa Pa a b p)
    (hk : k₁ < k₂) (hk₂ : k₂ < p.length) (hk₁pos : 1 ≤ k₁)
    (hadj : Adjacent Pa p[k₁ - 1] p[k₂]) :
    IsPathPa Pa a b (p.take k₁ ++ p.drop k₂) := by
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hpath
  have hk₁ : k₁ ≤ p.length := by omega
  have hqlen : (p.take k₁ ++ p.drop k₂).length = k₁ + (p.length - k₂) :=
    splice_length p k₁ k₂ hk₁
  have hinj : ∀ r s (hr : r < (p.take k₁ ++ p.drop k₂).length)
      (hs : s < (p.take k₁ ++ p.drop k₂).length),
      (p.take k₁ ++ p.drop k₂)[r] = (p.take k₁ ++ p.drop k₂)[s] → r = s := by
    intro r s hr hs hcon
    by_cases hrl : r < k₁ <;> by_cases hsl : s < k₁
    · have e1 := splice_getElem_of_lt p k₁ k₂ r hk₁ hr hrl
      have e2 := splice_getElem_of_lt p k₁ k₂ s hk₁ hs hsl
      rw [e1, e2] at hcon
      exact (hnodup.getElem_inj_iff).mp hcon
    · have e1 := splice_getElem_of_lt p k₁ k₂ r hk₁ hr hrl
      have e2 := splice_getElem_of_ge p k₁ k₂ s hk₁ hs (by omega)
      rw [e1, e2] at hcon
      have hrr := (hnodup.getElem_inj_iff).mp hcon
      omega
    · have e1 := splice_getElem_of_ge p k₁ k₂ r hk₁ hr (by omega)
      have e2 := splice_getElem_of_lt p k₁ k₂ s hk₁ hs hsl
      rw [e1, e2] at hcon
      have hrr := (hnodup.getElem_inj_iff).mp hcon
      omega
    · have e1 := splice_getElem_of_ge p k₁ k₂ r hk₁ hr (by omega)
      have e2 := splice_getElem_of_ge p k₁ k₂ s hk₁ hs (by omega)
      rw [e1, e2] at hcon
      have hrr := (hnodup.getElem_inj_iff).mp hcon
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro r s hr hs hlt hcon
    have hrr := hinj r s hr hs hcon
    omega
  · rw [List.isChain_iff_getElem]
    intro r hr
    rw [hqlen] at hr
    by_cases h1 : r + 1 < k₁
    · have hr' : r < (p.take k₁ ++ p.drop k₂).length := by omega
      have hr1 : r + 1 < (p.take k₁ ++ p.drop k₂).length := by omega
      have e1 := splice_getElem_of_lt p k₁ k₂ r hk₁ hr' (by omega)
      have e2 := splice_getElem_of_lt p k₁ k₂ (r + 1) hk₁ hr1 h1
      rw [e1, e2]
      exact List.IsChain.getElem hchain r (by omega)
    · by_cases h2 : r + 1 = k₁
      · have hr' : r < (p.take k₁ ++ p.drop k₂).length := by omega
        have hr1 : r + 1 < (p.take k₁ ++ p.drop k₂).length := by omega
        have e1 := splice_getElem_of_lt p k₁ k₂ r hk₁ hr' (by omega)
        have e2 := splice_getElem_of_ge p k₁ k₂ (r + 1) hk₁ hr1 (by omega)
        rw [e1, e2]
        have ez : k₂ + (r + 1 - k₁) = k₂ := by omega
        have er : r = k₁ - 1 := by omega
        simp only [ez]
        simp only [er]
        exact hadj
      · have hkr : k₁ ≤ r := by omega
        have hr' : r < (p.take k₁ ++ p.drop k₂).length := by omega
        have hr1 : r + 1 < (p.take k₁ ++ p.drop k₂).length := by omega
        have e1 := splice_getElem_of_ge p k₁ k₂ r hk₁ hr' hkr
        have e2 := splice_getElem_of_ge p k₁ k₂ (r + 1) hk₁ hr1 (by omega)
        rw [e1, e2]
        have es : k₂ + (r + 1 - k₁) = (k₂ + (r - k₁)) + 1 := by omega
        simp only [es]
        exact List.IsChain.getElem hchain (k₂ + (r - k₁)) (by omega)
  · rw [List.head?_append, List.head?_take]
    simp only [show k₁ ≠ 0 by omega]
    rw [hhead]
    rfl
  · rw [List.getLast?_append, List.getLast?_drop]
    simp only [show ¬ p.length ≤ k₂ by omega]
    rw [hlast]
    rfl

/-- Every triple of a take/drop splice is an old triple or a crossing triple. -/
private theorem splice_triple_transfer {V : Type*} (p : List V) (k₁ k₂ : ℕ)
    (hk : k₁ < k₂) (hk₂ : k₂ < p.length) (hk₁pos : 1 ≤ k₁)
    (t : ℕ) (ht : t + 2 < (p.take k₁ ++ p.drop k₂).length)
    (hk₁ : k₁ ≤ p.length := by omega)
    (hqlen : (p.take k₁ ++ p.drop k₂).length = k₁ + (p.length - k₂) :=
      splice_length p k₁ k₂ hk₁) :
    (∃ (k : ℕ) (_ : k + 2 < p.length), (p.take k₁ ++ p.drop k₂)[t] = p[k] ∧
      (p.take k₁ ++ p.drop k₂)[t + 1] = p[k + 1] ∧
      (p.take k₁ ++ p.drop k₂)[t + 2] = p[k + 2])
    ∨ (t + 1 = k₁ ∧ ∃ _ : k₂ + 1 < p.length, (p.take k₁ ++ p.drop k₂)[t] = p[t] ∧
      (p.take k₁ ++ p.drop k₂)[t + 1] = p[k₂] ∧
      (p.take k₁ ++ p.drop k₂)[t + 2] = p[k₂ + 1])
    ∨ (t + 2 = k₁ ∧ (p.take k₁ ++ p.drop k₂)[t] = p[t] ∧
      (p.take k₁ ++ p.drop k₂)[t + 1] = p[t + 1] ∧
      (p.take k₁ ++ p.drop k₂)[t + 2] = p[k₂]) := by
  rw [hqlen] at ht
  by_cases hpre : t + 2 < k₁
  · left
    refine ⟨t, by omega, ?_, ?_, ?_⟩
    · exact splice_getElem_of_lt p k₁ k₂ t hk₁ (by omega) (by omega)
    · exact splice_getElem_of_lt p k₁ k₂ (t + 1) hk₁ (by omega) (by omega)
    · exact splice_getElem_of_lt p k₁ k₂ (t + 2) hk₁ (by omega) (by omega)
  · by_cases hsuf : k₁ ≤ t
    · left
      have e1 := splice_getElem_of_ge p k₁ k₂ t hk₁ (by omega) hsuf
      have e2 := splice_getElem_of_ge p k₁ k₂ (t + 1) hk₁ (by omega) (by omega)
      have e3 := splice_getElem_of_ge p k₁ k₂ (t + 2) hk₁ (by omega) (by omega)
      have s1 : k₂ + (t + 1 - k₁) = (k₂ + (t - k₁)) + 1 := by omega
      have s2 : k₂ + (t + 2 - k₁) = (k₂ + (t - k₁)) + 2 := by omega
      simp only [s1] at e2
      simp only [s2] at e3
      exact ⟨k₂ + (t - k₁), by omega, e1, e2, e3⟩
    · by_cases hmid : t + 1 = k₁
      · right; left
        have e1 := splice_getElem_of_lt p k₁ k₂ t hk₁ (by omega) (by omega)
        have e2 := splice_getElem_of_ge p k₁ k₂ (t + 1) hk₁ (by omega) (by omega)
        have e3 := splice_getElem_of_ge p k₁ k₂ (t + 2) hk₁ (by omega) (by omega)
        have s1 : k₂ + (t + 1 - k₁) = k₂ := by omega
        have s2 : k₂ + (t + 2 - k₁) = k₂ + 1 := by omega
        simp only [s1] at e2
        simp only [s2] at e3
        exact ⟨hmid, by omega, e1, e2, e3⟩
      · right; right
        have e1 := splice_getElem_of_lt p k₁ k₂ t hk₁ (by omega) (by omega)
        have e2 := splice_getElem_of_lt p k₁ k₂ (t + 1) hk₁ (by omega) (by omega)
        have e3 := splice_getElem_of_ge p k₁ k₂ (t + 2) hk₁ (by omega) (by omega)
        have s3 : k₂ + (t + 2 - k₁) = k₂ := by omega
        simp only [s3] at e3
        exact ⟨by omega, e1, e2, e3⟩

/-- A collider at `x` with `y` elsewhere on an unblocked path shortens it. -/
private theorem exists_shorter_unblocked_of_collider_x_y_mem {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b u w : V} {p : List V}
    (hpath : IsPathPa Pa a b p) (hunblocked : ¬ PathBlockedPa Pa Z p)
    (hinfix : List.IsInfix [u, x, w] p)
    (hux : u ∈ Pa x) (hwx : w ∈ Pa x)
    (huy : u ≠ y) (hwy : w ≠ y)
    (hxZ : x ∉ Z)
    (hwit : ∃ d, d ∈ Z ∧ IsDescendantPa Pa y d)
    (hyp : y ∈ p) :
    ∃ q, IsPathPa Pa a b q ∧ ¬ PathBlockedPa Pa Z q ∧ q.length < p.length := by
  obtain ⟨d, hdZ, hdesc⟩ := hwit
  have hxyPa : x ∈ Pa y := by
    rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  have hynx : y ∉ Pa x :=
    y_not_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa'
  obtain ⟨i, hi, hiu, hix, hiw⟩ := infix_triple_getElem hinfix
  obtain ⟨j, hjlen, hjy⟩ := List.getElem_of_mem hyp
  have hji : j ≠ i := by
    intro hcon
    subst hcon
    rw [hiu] at hjy
    exact huy hjy
  have hji1 : j ≠ i + 1 := by
    intro hcon
    subst hcon
    rw [hix] at hjy
    exact hxy hjy
  have hji2 : j ≠ i + 2 := by
    intro hcon
    subst hcon
    rw [hiw] at hjy
    exact hwy hjy
  rcases lt_or_gt_of_ne hji1 with hjlt | hjgt
  · -- `y` before the collider: splice `take (j+1) ++ drop (i+1)`.
    have hjlti : j < i := by omega
    have hk : j + 1 < i + 1 := by omega
    have hadj : Adjacent Pa p[j + 1 - 1] p[i + 1] := by
      have e : j + 1 - 1 = j := by omega
      simp only [e, hjy, hix]
      exact Or.inr hxyPa
    have hpathQ := isPathPa_take_drop Pa hpath hk (by omega) (by omega) hadj
    have hqlen : (p.take (j + 1) ++ p.drop (i + 1)).length < p.length := by
      rw [splice_length p (j + 1) (i + 1) (by omega)]
      omega
    refine ⟨p.take (j + 1) ++ p.drop (i + 1), hpathQ, ?_, hqlen⟩
    intro hblocked
    obtain ⟨t, ht, hb⟩ := hblocked
    obtain htrans := splice_triple_transfer p (j + 1) (i + 1) hk (by omega) (by omega) t ht
    rcases htrans with ⟨k, hkk, e0, e1, e2⟩ | ⟨ht1, _hmid, e0, e1, e2⟩ | ⟨ht2, e0, e1, e2⟩
    · rw [e0, e1, e2] at hb
      exact hunblocked ⟨k, hkk, hb⟩
    · rw [e0, e1, e2] at hb
      have st : t = j := by omega
      simp only [st, hjy, hix, hiw] at hb
      unfold BlockedAtPa at hb
      rcases hb with ⟨hyx, -, -⟩ | ⟨-, hxZ'⟩
      · exact hynx hyx
      · exact hxZ hxZ'
    · rw [e0, e1, e2] at hb
      have st : t = j - 1 := by omega
      have f1 : j - 1 + 1 = j := by omega
      simp only [st, f1, hjy, hix] at hb
      unfold BlockedAtPa at hb
      rcases hb with ⟨-, -, hnodesc⟩ | ⟨hnc, hyZ⟩
      · exact hnodesc d hdesc hdZ
      · by_cases hprey : p[j - 1] ∈ Pa y
        · exact hnc ⟨hprey, hxyPa⟩
        · have hold : ¬ BlockedAtPa Pa Z p[j - 1] y p[j + 1] := by
            have hcon : ¬ BlockedAtPa Pa Z p[j - 1] p[j - 1 + 1] p[j - 1 + 2] :=
              fun h => hunblocked ⟨j - 1, by omega, h⟩
            have g1 : j - 1 + 1 = j := by omega
            have g2 : j - 1 + 2 = j + 1 := by omega
            simp only [g1, g2, hjy] at hcon
            exact hcon
          unfold BlockedAtPa at hold
          exact hold (Or.inr ⟨fun hcon => hprey hcon.1, hyZ⟩)
  · -- `y` after the collider: splice `take (i+2) ++ drop j`.
    have hk : i + 2 < j := by omega
    have hadj : Adjacent Pa p[i + 2 - 1] p[j] := by
      have e : i + 2 - 1 = i + 1 := by omega
      simp only [e, hix, hjy]
      exact Or.inl hxyPa
    have hpathQ := isPathPa_take_drop Pa hpath hk hjlen (by omega) hadj
    have hqlen : (p.take (i + 2) ++ p.drop j).length < p.length := by
      rw [splice_length p (i + 2) j (by omega)]
      omega
    refine ⟨p.take (i + 2) ++ p.drop j, hpathQ, ?_, hqlen⟩
    intro hblocked
    obtain ⟨t, ht, hb⟩ := hblocked
    obtain htrans := splice_triple_transfer p (i + 2) j hk hjlen (by omega) t ht
    rcases htrans with ⟨k, hkk, e0, e1, e2⟩ | ⟨ht1, hj1lt, e0, e1, e2⟩ | ⟨ht2, e0, e1, e2⟩
    · rw [e0, e1, e2] at hb
      exact hunblocked ⟨k, hkk, hb⟩
    · rw [e0, e1, e2] at hb
      have st : t = i + 1 := by omega
      simp only [st, hix, hjy] at hb
      unfold BlockedAtPa at hb
      rcases hb with ⟨-, -, hnodesc⟩ | ⟨hnc, hyZ⟩
      · exact hnodesc d hdesc hdZ
      · by_cases hnext : p[j + 1] ∈ Pa y
        · exact hnc ⟨hxyPa, hnext⟩
        · have hold : ¬ BlockedAtPa Pa Z p[j - 1] y p[j + 1] := by
            have hcon : ¬ BlockedAtPa Pa Z p[j - 1] p[j - 1 + 1] p[j - 1 + 2] :=
              fun h => hunblocked ⟨j - 1, by omega, h⟩
            have g1 : j - 1 + 1 = j := by omega
            have g2 : j - 1 + 2 = j + 1 := by omega
            simp only [g1, g2, hjy] at hcon
            exact hcon
          unfold BlockedAtPa at hold
          exact hold (Or.inr ⟨fun hcon => hnext hcon.2, hyZ⟩)
    · rw [e0, e1, e2] at hb
      have st : t = i := by omega
      simp only [st, hiu, hix, hjy] at hb
      unfold BlockedAtPa at hb
      rcases hb with ⟨-, hyx, -⟩ | ⟨-, hxZ'⟩
      · exact hynx hyx
      · exact hxZ hxZ'

/-- An unblocked path in `Pa` yields an unblocked path in `Pa'`. -/
private theorem exists_unblocked_transport {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa')
    (x y : V) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x))
    (hPa' : Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
    {Z : Set V} {a b : V} (p : List V) (hpath : IsPathPa Pa a b p)
    (hunblocked : ¬ PathBlockedPa Pa Z p) :
    ∃ q, IsPathPa Pa' a b q ∧ ¬ PathBlockedPa Pa' Z q := by
  have aux : ∀ n p, p.length ≤ n → IsPathPa Pa a b p → ¬ PathBlockedPa Pa Z p →
      ∃ q, IsPathPa Pa' a b q ∧ ¬ PathBlockedPa Pa' Z q := by
    intro n
    induction n with
    | zero =>
      intro p hlen hpath hunblocked
      have h0 : p.length = 0 := Nat.le_zero.mp hlen
      have hp : p = [] := List.length_eq_zero_iff.mp h0
      subst hp
      obtain ⟨-, -, hhead, -⟩ := hpath
      simp at hhead
    | succ n ih =>
      intro p hlen hpath hunblocked
      have hpath' : IsPathPa Pa' a b p :=
        (isPathPa_of_coveredReversal h hc x y hxy hPay hPa').mpr hpath
      rcases Classical.em (PathBlockedPa Pa' Z p) with hblocked' | hblocked'
      · obtain ⟨u, m, w, hinfix, hblocked_at'⟩ :=
          (pathBlockedPa_iff Pa' Z p).mp hblocked'
        have hnotblocked_at : ¬ BlockedAtPa Pa Z u m w := by
          intro hcon
          exact hunblocked ((pathBlockedPa_iff Pa Z p).mpr ⟨u, m, w, hinfix, hcon⟩)
        have hxyPa : x ∈ Pa y := by
          rw [hPay]; exact Finset.mem_insert_self x (Pa x)
        have hynx : y ∉ Pa x :=
          y_not_mem_pa_x_of_coveredReversal h hc x y hxy hPay hPa'
        have hxx : x ∉ Pa x := fun hx => h x (Relation.TransGen.single hx)
        have hpath0 := hpath
        obtain ⟨hnodup, -, -, -⟩ := hpath
        obtain ⟨i, hi, e0, e1, e2⟩ := infix_triple_getElem hinfix
        have hpw := List.nodup_iff_pairwise_ne.mp hnodup
        have hpw' := List.pairwise_iff_getElem.mp hpw
        have hne_um : u ≠ m := by
          have h : p[i] ≠ p[i + 1] := hpw' i (i + 1) (by omega) (by omega) (by omega)
          rwa [e0, e1] at h
        have hne_mw : m ≠ w := by
          have h : p[i + 1] ≠ p[i + 2] :=
            hpw' (i + 1) (i + 2) (by omega) (by omega) (by omega)
          rwa [e1, e2] at h
        have hne_uw : u ≠ w := by
          have h : p[i] ≠ p[i + 2] := hpw' i (i + 2) (by omega) (by omega) (by omega)
          rwa [e0, e2] at h
        by_cases hmx : x = m
        · subst hmx
          unfold BlockedAtPa at hblocked_at' hnotblocked_at
          by_cases huy : y = u
          · subst huy
            have hxZ : x ∉ Z := by
              intro hxZ'
              exact hnotblocked_at (Or.inr ⟨fun hcon => hynx hcon.1, hxZ'⟩)
            rcases hblocked_at' with ⟨-, hwx', -⟩ | ⟨-, hxZ'⟩
            · have hwx : w ∈ Pa x := by
                rcases (mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa').mp hwx'
                  with heq | h
                · exact absurd heq.symm hne_uw
                · exact h
              obtain ⟨q, hqpath, hqunblocked, hqlen⟩ :=
                exists_shorter_unblocked_of_y_x_w h hc x y hxy hPay hPa' hpath0
                  hunblocked hwx hinfix
              exact ih q (by omega) hqpath hqunblocked
            · exact (hxZ hxZ').elim
          · by_cases hwy : y = w
            · subst hwy
              have hxZ : x ∉ Z := by
                intro hxZ'
                exact hnotblocked_at (Or.inr ⟨fun hcon => hynx hcon.2, hxZ'⟩)
              rcases hblocked_at' with ⟨hux', -, -⟩ | ⟨-, hxZ'⟩
              · have hux : u ∈ Pa x := by
                  rcases (mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa').mp hux'
                    with heq | h
                  · exact absurd heq hne_uw
                  · exact h
                obtain ⟨q, hqpath, hqunblocked, hqlen⟩ :=
                  exists_shorter_unblocked_of_u_x_y h hc x y hxy hPay hPa' hpath0
                    hunblocked hux hinfix
                exact ih q (by omega) hqpath hqunblocked
              · exact (hxZ hxZ').elim
            · have eux : u ∈ Pa' x ↔ u ∈ Pa x := by
                rw [mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa']
                constructor
                · rintro (heq | h)
                  · exact absurd heq (Ne.symm huy)
                  · exact h
                · intro h; exact Or.inr h
              have ewx : w ∈ Pa' x ↔ w ∈ Pa x := by
                rw [mem_pa'_of_coveredReversal_x h hc x y hxy hPay hPa']
                constructor
                · rintro (heq | h)
                  · exact absurd heq (Ne.symm hwy)
                  · exact h
                · intro h; exact Or.inr h
              have coll_iff : (u ∈ Pa' x ∧ w ∈ Pa' x) ↔ (u ∈ Pa x ∧ w ∈ Pa x) :=
                and_congr eux ewx
              rcases hblocked_at' with ⟨hux', hwx', hnone'⟩ | ⟨hncoll', hxZ'⟩
              · have hux : u ∈ Pa x := eux.mp hux'
                have hwx : w ∈ Pa x := ewx.mp hwx'
                have hxZ : x ∉ Z := hnone' x Relation.ReflTransGen.refl
                have head_split : ∀ {d}, Relation.TransGen (fun u w => u ∈ Pa w) x d →
                    ∃ v1, x ∈ Pa v1 ∧ IsDescendantPa Pa v1 d := by
                  intro d htr
                  induction htr with
                  | single h => exact ⟨_, h, Relation.ReflTransGen.refl⟩
                  | tail _ h2 ih =>
                    obtain ⟨v1, g1, g2⟩ := ih
                    exact ⟨v1, g1, Relation.ReflTransGen.tail g2 h2⟩
                obtain ⟨d, hdZ, hd⟩ : ∃ d, d ∈ Z ∧ IsDescendantPa Pa x d := by
                  by_contra hcon
                  exact hnotblocked_at
                    (Or.inl ⟨hux, hwx, fun d hd hdZ => hcon ⟨d, hdZ, hd⟩⟩)
                have hdr : Relation.ReflTransGen (fun u w => u ∈ Pa w) x d := hd
                rcases Relation.reflTransGen_iff_eq_or_transGen.mp hdr with rfl | htrans
                · exact (hxZ hdZ).elim
                · obtain ⟨v1, hxv1, hrest⟩ := head_split htrans
                  have hv1x : v1 ≠ x := by
                    intro heq
                    rw [heq] at hxv1
                    exact hxx hxv1
                  by_cases hv1y : y = v1
                  · subst hv1y
                    have hwit : ∃ d, d ∈ Z ∧ IsDescendantPa Pa y d := ⟨d, hdZ, hrest⟩
                    by_cases hyp : y ∈ p
                    · obtain ⟨q, hqpath, hqunblocked, hqlen⟩ :=
                        exists_shorter_unblocked_of_collider_x_y_mem h hc x y hxy hPay
                          hPa' hpath0 hunblocked hinfix hux hwx (Ne.symm huy)
                          (Ne.symm hwy) hxZ hwit hyp
                      exact ih q (by omega) hqpath hqunblocked
                    · have hpre : p[i + 1 - 1] ∈ Pa x := by
                        show p[i] ∈ Pa x
                        rw [e0]; exact hux
                      have hsuc : p[i + 1 + 1] ∈ Pa x := by
                        show p[i + 2] ∈ Pa x
                        rw [e2]; exact hwx
                      have hrep := replace_x_with_y_unblocked h hc x y hxy hPay hPa'
                        hpath0 hunblocked (i := i + 1) (by omega) e1 (by omega) (by omega)
                        hpre hsuc hyp hwit hxZ
                      exact ⟨_, hrep.1, hrep.2⟩
                  · have hd' : IsDescendantPa Pa' x d :=
                      (isDescendantPa_x_iff_of_coveredReversal h hc x y hxy hPay hPa').mpr
                        (Or.inr ⟨v1, hv1x, Ne.symm hv1y, hxv1, hrest⟩)
                    exact ((hnone' d hd') hdZ).elim
              · have hncoll : ¬(u ∈ Pa x ∧ w ∈ Pa x) :=
                  fun hcon => hncoll' (coll_iff.mpr hcon)
                have hxZ : x ∉ Z := fun hxZ' => hnotblocked_at (Or.inr ⟨hncoll, hxZ'⟩)
                exact (hxZ hxZ').elim
        · by_cases hmy : y = m
          · subst hmy
            unfold BlockedAtPa at hblocked_at' hnotblocked_at
            by_cases hux : x = u
            · subst hux
              have hxny' : x ∉ Pa' y := by
                rw [mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa']
                exact hxx
              have hyZ : y ∈ Z := by
                rcases hblocked_at' with ⟨h1, -, -⟩ | ⟨-, hyZ⟩
                · exact absurd h1 hxny'
                · exact hyZ
              by_cases hwx : w ∈ Pa x
              · obtain ⟨q, hqpath, hqunblocked, hqlen⟩ :=
                  exists_shorter_unblocked_of_x_y_w h hc x y hxy hPay hPa' hpath0
                    hunblocked hwx hyZ hinfix
                exact ih q (by omega) hqpath hqunblocked
              · have hwx' : w ≠ x := Ne.symm hne_uw
                have hwy : w ∉ Pa y := by
                  rw [hPay, Finset.mem_insert]
                  rintro (heq | h)
                  · exact hwx' heq
                  · exact hwx h
                have hyZn : y ∉ Z := by
                  intro hyZ'
                  exact hnotblocked_at (Or.inr ⟨fun hcon => hwy hcon.2, hyZ'⟩)
                exact (hyZn hyZ).elim
            · by_cases hwx : x = w
              · subst hwx
                have hxny' : x ∉ Pa' y := by
                  rw [mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa']
                  exact hxx
                have hyZ : y ∈ Z := by
                  rcases hblocked_at' with ⟨-, h2, -⟩ | ⟨-, hyZ⟩
                  · exact absurd h2 hxny'
                  · exact hyZ
                by_cases huxm : u ∈ Pa x
                · obtain ⟨q, hqpath, hqunblocked, hqlen⟩ :=
                    exists_shorter_unblocked_of_u_y_x h hc x y hxy hPay hPa' hpath0
                      hunblocked huxm hyZ hinfix
                  exact ih q (by omega) hqpath hqunblocked
                · have hux' : u ≠ x := hne_uw
                  have huy : u ∉ Pa y := by
                    rw [hPay, Finset.mem_insert]
                    rintro (heq | h)
                    · exact hux' heq
                    · exact huxm h
                  have hyZn : y ∉ Z := by
                    intro hyZ'
                    exact hnotblocked_at (Or.inr ⟨fun hcon => huy hcon.1, hyZ'⟩)
                  exact (hyZn hyZ).elim
              · have euy : u ∈ Pa' y ↔ u ∈ Pa y := by
                  rw [mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa', hPay,
                    Finset.mem_insert]
                  constructor
                  · intro h'; exact Or.inr h'
                  · rintro (heq | h')
                    · exact absurd heq (Ne.symm hux)
                    · exact h'
                have ewy : w ∈ Pa' y ↔ w ∈ Pa y := by
                  rw [mem_pa'_of_coveredReversal_y h hc x y hxy hPay hPa', hPay,
                    Finset.mem_insert]
                  constructor
                  · intro h'; exact Or.inr h'
                  · rintro (heq | h')
                    · exact absurd heq (Ne.symm hwx)
                    · exact h'
                have coll_iff : (u ∈ Pa' y ∧ w ∈ Pa' y) ↔ (u ∈ Pa y ∧ w ∈ Pa y) :=
                  and_congr euy ewy
                rcases hblocked_at' with ⟨huy', hwy', hnone'⟩ | ⟨hncoll', hyZ⟩
                · have huy : u ∈ Pa y := euy.mp huy'
                  have hwy : w ∈ Pa y := ewy.mp hwy'
                  obtain ⟨d, hd, hdZ⟩ : ∃ d, IsDescendantPa Pa y d ∧ d ∈ Z := by
                    by_contra hcon
                    exact hnotblocked_at
                      (Or.inl ⟨huy, hwy, fun d hd hdZ => hcon ⟨d, hd, hdZ⟩⟩)
                  have hd' : IsDescendantPa Pa' y d :=
                    isDescendantPa_y_of_coveredReversal h hc x y hxy hPay hPa' hd
                  exact ((hnone' d hd') hdZ).elim
                · have hncoll : ¬(u ∈ Pa y ∧ w ∈ Pa y) :=
                    fun hcon => hncoll' (coll_iff.mpr hcon)
                  exact (hnotblocked_at (Or.inr ⟨hncoll, hyZ⟩)).elim
          · exact (hnotblocked_at
              ((blockedAtPa_of_coveredReversal_ne h hc x y hxy hPay hPa' (Ne.symm hmx)
                (Ne.symm hmy)).mp hblocked_at')).elim
      · exact ⟨p, hpath', hblocked'⟩
  exact aux p.length p le_rfl hpath hunblocked

/-- A covered reversal of an acyclic structure preserves every d-separation. -/
theorem dSeparatedPa_iff_of_coveredReversal {V : Type*} [DecidableEq V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (hc : CoveredReversal Pa Pa') (X Y Z : Set V) :
    DSeparatedPa Pa X Y Z ↔ DSeparatedPa Pa' X Y Z := by
      have hc0 := hc
      obtain ⟨x, y, hxy, hPay, hPa'⟩ := hc
      have h' : IsAcyclic Pa' := IsAcyclic.coveredReversal h hc0
      have hc' : CoveredReversal Pa' Pa :=
        coveredReversal_symm_data h hc0 x y hxy hPay hPa'
      have hc0' := hc'
      obtain ⟨x', y', hxy', hPay', hPa''⟩ := hc'
      constructor
      · intro hDS
        unfold DSeparatedPa
        intro a ha b hb p hp
        by_contra hnb
        obtain ⟨q, hq, hqnb⟩ :=
          exists_unblocked_transport h' hc0' x' y' hxy' hPay' hPa'' p hp hnb
        exact hqnb (hDS a ha b hb q hq)
      · intro hDS
        unfold DSeparatedPa
        intro a ha b hb p hp
        by_contra hnb
        obtain ⟨q, hq, hqnb⟩ :=
          exists_unblocked_transport h hc0 x y hxy hPay hPa' p hp hnb
        exact hqnb (hDS a ha b hb q hq)

/-- , the (<=) direction of Verma and Pearl (1990), Theorem 1, for d-separation: two
acyclic structures with the same skeleton and the same v-structures have the same
d-separations. -/
theorem dSeparatedPa_iff_of_markovEquivalent {V : Type*} [DecidableEq V] [Finite V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    (hskel : ∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w)
    (hv : ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) (X Y Z : Set V) :
    DSeparatedPa Pa X Y Z ↔ DSeparatedPa Pa' X Y Z := by
      have chain := reflTransGen_coveredReversal_of_markovEquivalent h h' hskel hv
      have acyc : ∀ {Q}, Relation.ReflTransGen CoveredReversal Pa Q → IsAcyclic Q := by
        intro Q hQ
        induction hQ with
        | refl => exact h
        | tail _ hstep ih => exact IsAcyclic.coveredReversal ih hstep
      have aux : ∀ {Q}, Relation.ReflTransGen CoveredReversal Pa Q →
          (DSeparatedPa Pa X Y Z ↔ DSeparatedPa Q X Y Z) := by
        intro Q hQ
        induction hQ with
        | refl => exact Iff.rfl
        | tail hprev hstep ih =>
          exact ih.trans (dSeparatedPa_iff_of_coveredReversal (acyc hprev) hstep X Y Z)
      exact aux chain

/-! ### T8: the `BayesNet` corollary, with a relabeling -/

/-- Two networks on `Fin n` whose structures have the same skeleton and the same
v-structures along a relabeling `e` have the same d-separations, transported along `e`. -/
theorem BayesNet.dSeparated_iff_of_markovEquivalent {n : ℕ} (b : BayesNet α n)
    (b' : BayesNet β n) (e : Fin n ≃ Fin n) (hskel : ∀ i j, b.Adj i j ↔ b'.Adj (e i) (e j))
    (hv : ∀ i j k, IsVStructure b.toPa i j k ↔ IsVStructure b'.toPa (e i) (e j) (e k))
    (X Y Z : Set (Fin n)) :
    b.DSeparated X Y Z ↔ b'.DSeparated (e '' X) (e '' Y) (e '' Z) := by
      rw [BayesNet.dSeparated_iff_dSeparatedPa_toPa b,
        BayesNet.dSeparated_iff_dSeparatedPa_toPa b']
      have hA : IsAcyclic (relabel e b.toPa) := (isAcyclic_relabel e).mpr (isAcyclic_toPa b)
      have hA' : IsAcyclic b'.toPa := isAcyclic_toPa b'
      have hskel' : ∀ u w, Adjacent (relabel e b.toPa) u w ↔ Adjacent b'.toPa u w := by
        intro u w
        obtain ⟨i, rfl⟩ := e.surjective u
        obtain ⟨j, rfl⟩ := e.surjective w
        exact (adjacent_relabel e i j).trans
          ((adjacent_toPa_iff b).trans ((hskel i j).trans (adjacent_toPa_iff b').symm))
      have hv' : ∀ u w z, IsVStructure (relabel e b.toPa) u w z ↔
          IsVStructure b'.toPa u w z := by
        intro u w z
        obtain ⟨i, rfl⟩ := e.surjective u
        obtain ⟨j, rfl⟩ := e.surjective w
        obtain ⟨k, rfl⟩ := e.surjective z
        exact (isVStructure_relabel e i j k).trans (hv i j k)
      exact (dSeparatedPa_relabel e).symm.trans
        (dSeparatedPa_iff_of_markovEquivalent hA hA' hskel' hv' (e '' X) (e '' Y) (e '' Z))

end Cslib.MachineLearning.GraphicalModels
