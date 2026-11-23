/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.VermaPearl

/-!
# Verma and Pearl: same d-separations give the same skeleton and v-structures

The forward direction of Verma and Pearl (1990, \"Equivalence and synthesis of
causal models\", Theorem 1; arXiv:1304.1108), complementing `VermaPearl.lean`:
two acyclic parent-set structures with the same d-separations have the same
skeleton and the same v-structures. Non-adjacent vertices are separated by
the parents of the later one (Lemma 1), and a middle vertex of an unshielded
triple is a collider exactly when it lies in no separator of the endpoints
(Lemma 2). Together with the converse in `VermaPearl.lean` this gives
`markovEquivalent_iff_dSeparatedPa_iff` on structures and
`BayesNet.markovEquivalent_iff_dSeparated_iff` on networks along a
relabeling.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset BayesianDirichlet

variable {α β : Type*}

-- Symmetry of the Pa mirror (mirrors of the BayesNet symmetry family in CausalBayesNet)
/-- toward Verma-Pearl Lemma 1 (arXiv:1304.1108): blocking at `u, m, w` ignores direction. -/
theorem blockedAtPa_comm {V : Type*} {Pa : V → Finset V} {Z : Set V} {u m w : V} :
    BlockedAtPa Pa Z u m w ↔ BlockedAtPa Pa Z w m u := by
  unfold BlockedAtPa
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩

/-- toward Verma-Pearl Lemma 1 (arXiv:1304.1108): the reverse of a path is a path. -/
theorem isPathPa_reverse {V : Type*} {Pa : V → Finset V} {x y : V} {p : List V}
    (h : IsPathPa Pa x y p) : IsPathPa Pa y x p.reverse := by
  unfold IsPathPa at h ⊢
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := h
  refine ⟨List.nodup_reverse.mpr hnodup, ?_, ?_, ?_⟩
  · rw [List.isChain_reverse]
    have hsym : (fun a b => Adjacent Pa b a) = Adjacent Pa := by
      funext a b
      exact propext or_comm
    rw [hsym]
    exact hchain
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

/-- toward Verma-Pearl Lemma 1 (arXiv:1304.1108): reversing keeps a path blocked. -/
theorem pathBlockedPa_reverse {V : Type*} {Pa : V → Finset V} {Z : Set V} {p : List V}
    (h : PathBlockedPa Pa Z p) : PathBlockedPa Pa Z p.reverse := by
  unfold PathBlockedPa at h ⊢
  obtain ⟨i, hi, hblock⟩ := h
  refine ⟨p.length - 3 - i, by rw [List.length_reverse]; omega, ?_⟩
  have hj : p.length - 1 - (p.length - 3 - i) = i + 2 := by omega
  have hj1 : p.length - 1 - (p.length - 3 - i + 1) = i + 1 := by omega
  have hj2 : p.length - 1 - (p.length - 3 - i + 2) = i := by omega
  rw [List.getElem_reverse, List.getElem_reverse, List.getElem_reverse]
  simp only [hj, hj1, hj2]
  exact blockedAtPa_comm.mpr hblock

/-- toward Verma-Pearl Lemma 1 (arXiv:1304.1108): d-separation is symmetric. -/
theorem DSeparatedPa.symm {V : Type*} {Pa : V → Finset V} {X Y Z : Set V}
    (h : DSeparatedPa Pa X Y Z) : DSeparatedPa Pa Y X Z := by
  unfold DSeparatedPa at h ⊢
  intro y hy x hx p hp
  have hpr : IsPathPa Pa x y p.reverse := isPathPa_reverse hp
  have hpb : PathBlockedPa Pa Z p.reverse := h x hx y hy p.reverse hpr
  have h2 := pathBlockedPa_reverse hpb
  rwa [List.reverse_reverse] at h2

-- Adjacent vertices are never d-separated (Lemma 1, (1) => (2)); no acyclicity needed
/-- Verma-Pearl Lemma 1 (1) ⇒ (2) (arXiv:1304.1108): adjacent ⇒ unseparable. -/
theorem not_dSeparatedPa_of_adjacent {V : Type*} {Pa : V → Finset V} {u w : V}
    (h : Adjacent Pa u w) (Z : Set V) : ¬DSeparatedPa Pa {u} {w} Z := by
  intro hds
  unfold DSeparatedPa at hds
  by_cases huw : u = w
  · subst huw
    have hpath : IsPathPa Pa u u [u] := by
      unfold IsPathPa
      exact ⟨by simp, List.isChain_singleton u, rfl, rfl⟩
    have hpb := hds u (Set.mem_singleton u) u (Set.mem_singleton u) [u] hpath
    unfold PathBlockedPa at hpb
    obtain ⟨i, hi, -⟩ := hpb
    have hlen : ([u] : List V).length = 1 := rfl
    omega
  · have hpath : IsPathPa Pa u w [u, w] := by
      unfold IsPathPa
      refine ⟨by simpa using huw, ?_, rfl, rfl⟩
      rw [List.isChain_cons]
      refine ⟨?_, List.isChain_singleton w⟩
      intro y hy
      simp at hy
      subst hy
      exact h
    have hpb := hds u (Set.mem_singleton u) w (Set.mem_singleton w) [u, w] hpath
    unfold PathBlockedPa at hpb
    obtain ⟨i, hi, -⟩ := hpb
    have hlen : ([u, w] : List V).length = 2 := rfl
    omega

private lemma localMarkov_aux_cycle {V : Type*} {Pa : V → Finset V}
    (h : IsAcyclic Pa) {i a : V} (hmem : a ∈ Pa i)
    (hdesc : IsDescendantPa Pa i a) : False :=
  h i (Relation.TransGen.tail' hdesc hmem)

private lemma localMarkov_aux_forward {V : Type*} {Pa : V → Finset V}
    (hacy : IsAcyclic Pa) (i : V) :
    ∀ (q : List V) (u m : V), IsDescendantPa Pa i m → u ∈ Pa m →
      (u :: m :: q).IsChain (Adjacent Pa) →
      (∀ (k : ℕ) (h : k + 2 < (u :: m :: q).length),
        ¬ BlockedAtPa Pa ↑(Pa i) (u :: m :: q)[k] (u :: m :: q)[k + 1]
          (u :: m :: q)[k + 2]) →
      ∀ y, (m :: q).getLast? = some y → IsDescendantPa Pa i y
  | [], u, m, hm, _, _, _, y, hy => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hy
    exact hy ▸ hm
  | w :: q, u, m, hm, hum, hch, hnb, y, hy => by
    have hmw : Adjacent Pa m w :=
      (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2).1
    rcases hmw with hmw | hwm
    · refine localMarkov_aux_forward hacy i q m w
        (Relation.ReflTransGen.tail hm hmw) hmw
        (List.isChain_cons_cons.1 hch).2 (fun k hk => ?_) y (by simpa using hy)
      have := hnb (k + 1) (by simp at hk ⊢; omega)
      simpa using this
    · exfalso
      refine hnb 0 (by simp) (Or.inl ⟨hum, hwm, fun d hd hdZ => ?_⟩)
      have hid : IsDescendantPa Pa i d :=
        Relation.ReflTransGen.trans hm hd
      exact localMarkov_aux_cycle hacy (Finset.mem_coe.mp hdZ) hid

-- Local Markov property for structures (mirror of BayesNet.dSeparated_localMarkov)
/-- toward Verma-Pearl Lemma 1 (2) ⇒ (1) (arXiv:1304.1108): the local Markov separator. -/
theorem dSeparatedPa_localMarkov {V : Type*} {Pa : V → Finset V} (h : IsAcyclic Pa) (w : V) :
    DSeparatedPa Pa {w} {u | ¬IsDescendantPa Pa w u ∧ u ∉ Pa w} ↑(Pa w) := by
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  obtain ⟨hyd, hypa⟩ := hy
  obtain ⟨hnd, hch, hh, hlast⟩ := hp
  match p, hnd, hch, hh, hlast with
  | [], _, _, hh, _ => exact absurd hh (by simp)
  | [a], _, _, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hh hlast
    exact absurd (hlast ▸ hh ▸ Relation.ReflTransGen.refl) hyd
  | a :: v :: rest, hnd, hch, hh, hlast =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hadj : Adjacent Pa a v := (List.isChain_cons_cons.1 hch).1
    rcases hadj with hav | hva
    · by_contra hnb
      simp only [PathBlockedPa, not_exists] at hnb
      exact hyd (localMarkov_aux_forward h a rest a v
        (Relation.ReflTransGen.single hav) hav hch hnb y (by simpa using hlast))
    · match rest, hch, hlast with
      | [], _, hlast =>
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
          at hlast
        exact absurd (hlast ▸ hva) hypa
      | z :: rest', _, _ =>
        have hnot : ¬a ∈ Pa v := fun hcontra =>
          localMarkov_aux_cycle h hva (Relation.ReflTransGen.single hcontra)
        exact ⟨0, by simp, Or.inr ⟨fun hh => hnot hh.1, Finset.mem_coe.mpr hva⟩⟩

-- The parent separator: parents of the later vertex (w later: u is not a descendant of w)
/-- Verma-Pearl Lemma 1 (2) ⇒ (1) (arXiv:1304.1108) with `Pa w` in place of the combined parent set. -/
theorem dSeparatedPa_parents_of_not_adjacent {V : Type*} {Pa : V → Finset V} (h : IsAcyclic Pa)
    {u w : V} (hnd : ¬IsDescendantPa Pa w u) (hna : ¬Adjacent Pa u w) :
    DSeparatedPa Pa {u} {w} ↑(Pa w) := by
  have hF2 := dSeparatedPa_localMarkov h w
  have hu : u ∈ {u | ¬IsDescendantPa Pa w u ∧ u ∉ Pa w} :=
    ⟨hnd, fun hm => hna (Or.inl hm)⟩
  have h1 : DSeparatedPa Pa {w} {u} ↑(Pa w) := by
    intro x hx y hy p hp
    simp only [Set.mem_singleton_iff] at hx hy
    rw [hx, hy] at hp
    exact hF2 w (Set.mem_singleton w) u hu p hp
  exact DSeparatedPa.symm h1

-- Lemma 1, (1) <=> (2), for structures
/-- Verma-Pearl Lemma 1 (1) ⇔ (2) (arXiv:1304.1108), for distinct nodes. -/
theorem adjacent_iff_forall_not_dSeparatedPa {V : Type*} {Pa : V → Finset V} (h : IsAcyclic Pa)
    {u w : V} (huw : u ≠ w) : Adjacent Pa u w ↔ ∀ Z, ¬DSeparatedPa Pa {u} {w} Z := by
  constructor
  · intro hadj Z
    exact not_dSeparatedPa_of_adjacent hadj Z
  · intro hall
    by_contra hna
    by_cases hwu : IsDescendantPa Pa w u
    · by_cases huw_desc : IsDescendantPa Pa u w
      · have toT : ∀ {a b : V}, Relation.ReflTransGen (fun x y => x ∈ Pa y) a b → a ≠ b →
            Relation.TransGen (fun x y => x ∈ Pa y) a b := by
          intro a b hab hne
          cases hab with
          | refl => exact absurd rfl hne
          | tail h' e => exact Relation.TransGen.tail' h' e
        exact h u ((toT huw_desc huw).trans (toT hwu huw.symm))
      · have hna' : ¬Adjacent Pa w u := fun hcon => hna (or_comm.mp hcon)
        have hsep := DSeparatedPa.symm
          (dSeparatedPa_parents_of_not_adjacent h huw_desc hna')
        exact absurd hsep (hall _)
    · exact absurd (dSeparatedPa_parents_of_not_adjacent h hwu hna) (hall _)

-- Collider vs separator (Lemma 2, per-separator form; the PC-orientation interface)
/-- Verma-Pearl Lemma 2 (arXiv:1304.1108), per separator: collider iff `c ∉ S`. -/
theorem collider_iff_not_mem_of_dSeparatedPa {V : Type*} {Pa : V → Finset V} (h : IsAcyclic Pa)
    {a c b : V} (hac : Adjacent Pa a c) (hcb : Adjacent Pa c b) (hab : a ≠ b) {S : Set V}
    (hS : DSeparatedPa Pa {a} {b} S) : (a ∈ Pa c ∧ b ∈ Pa c) ↔ c ∉ S := by
  have hanc : a ≠ c := by
    rintro rfl
    rcases hac with hself | hself <;> exact h _ (Relation.TransGen.single hself)
  have hcnb : c ≠ b := by
    rintro rfl
    rcases hcb with hself | hself <;> exact h _ (Relation.TransGen.single hself)
  have hpath : IsPathPa Pa a b [a, c, b] := by
    unfold IsPathPa
    refine ⟨?_, ?_, rfl, rfl⟩
    · simp [hanc, hcnb, hab]
    · rw [List.isChain_cons, List.isChain_cons]
      refine ⟨?_, ?_, List.isChain_singleton b⟩
      · intro y hy
        simp at hy
        subst hy
        exact hac
      · intro y hy
        simp at hy
        subst hy
        exact hcb
  have hpb := hS a (Set.mem_singleton a) b (Set.mem_singleton b) [a, c, b] hpath
  unfold PathBlockedPa at hpb
  obtain ⟨i, hi, hblock⟩ := hpb
  have hlen : ([a, c, b] : List V).length = 3 := rfl
  have hi0 : i = 0 := by omega
  subst hi0
  have e0 : ([a, c, b] : List V)[0] = a := rfl
  have e1 : ([a, c, b] : List V)[0 + 1] = c := rfl
  have e2 : ([a, c, b] : List V)[0 + 2] = b := rfl
  rw [e0, e1, e2] at hblock
  unfold BlockedAtPa at hblock
  constructor
  · rintro ⟨ha, hb⟩ hmem
    rcases hblock with ⟨-, -, hall⟩ | ⟨hnc, -⟩
    · exact hall c Relation.ReflTransGen.refl hmem
    · exact hnc ⟨ha, hb⟩
  · intro hcnS
    by_contra hnc
    rcases hblock with ⟨ha, hb, -⟩ | ⟨-, hmem⟩
    · exact hnc ⟨ha, hb⟩
    · exact hcnS hmem

-- (=>) direction, skeleton
/-- Verma-Pearl Theorem 1 (⇒) (arXiv:1304.1108): same d-separations, same links. -/
theorem adjacent_iff_of_dSeparatedPa_iff {V : Type*} {Pa Pa' : V → Finset V}
    (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    (hds : ∀ X Y Z, DSeparatedPa Pa X Y Z ↔ DSeparatedPa Pa' X Y Z) (u w : V) :
    Adjacent Pa u w ↔ Adjacent Pa' u w := by
  by_cases huw : u = w
  · rw [huw]
    have hPa : ¬Adjacent Pa w w := by
      rintro (hmem | hmem) <;> exact h w (Relation.TransGen.single hmem)
    have hPa' : ¬Adjacent Pa' w w := by
      rintro (hmem | hmem) <;> exact h' w (Relation.TransGen.single hmem)
    exact iff_of_false hPa hPa'
  · rw [adjacent_iff_forall_not_dSeparatedPa h huw,
      adjacent_iff_forall_not_dSeparatedPa h' huw]
    constructor
    · intro hall Z hcon
      exact hall Z ((hds {u} {w} Z).mpr hcon)
    · intro hall Z hcon
      exact hall Z ((hds {u} {w} Z).mp hcon)

-- (=>) direction, v-structures
/-- Verma-Pearl Theorem 1 (⇒) (arXiv:1304.1108): same uncoupled head-to-head nodes. -/
theorem isVStructure_iff_of_dSeparatedPa_iff {V : Type*} {Pa Pa' : V → Finset V}
    (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    (hds : ∀ X Y Z, DSeparatedPa Pa X Y Z ↔ DSeparatedPa Pa' X Y Z) (u w z : V) :
    IsVStructure Pa u w z ↔ IsVStructure Pa' u w z := by
  unfold IsVStructure
  have hF6_uz : Adjacent Pa u z ↔ Adjacent Pa' u z :=
    adjacent_iff_of_dSeparatedPa_iff h h' hds u z
  have hF6_uw : Adjacent Pa u w ↔ Adjacent Pa' u w :=
    adjacent_iff_of_dSeparatedPa_iff h h' hds u w
  have hF6_wz : Adjacent Pa w z ↔ Adjacent Pa' w z :=
    adjacent_iff_of_dSeparatedPa_iff h h' hds w z
  constructor
  · rintro ⟨huz, huw, hzw, hna⟩
    have hna' : ¬Adjacent Pa' u z := fun hcon => hna (hF6_uz.mpr hcon)
    have hex : ∃ S, DSeparatedPa Pa {u} {z} S := by
      by_contra hc
      exact hna ((adjacent_iff_forall_not_dSeparatedPa h huz).mpr
        (fun Z hZ => hc ⟨Z, hZ⟩))
    obtain ⟨S, hS⟩ := hex
    have hF5 := collider_iff_not_mem_of_dSeparatedPa h (Or.inl huw : Adjacent Pa u w)
      (Or.inr hzw : Adjacent Pa w z) huz hS
    have hwS : w ∉ S := hF5.mp ⟨huw, hzw⟩
    have hS' : DSeparatedPa Pa' {u} {z} S := (hds {u} {z} S).mp hS
    have hF5' := collider_iff_not_mem_of_dSeparatedPa h' (hF6_uw.mp (Or.inl huw))
      (hF6_wz.mp (Or.inr hzw)) huz hS'
    have hmem' : u ∈ Pa' w ∧ z ∈ Pa' w := hF5'.mpr hwS
    exact ⟨huz, hmem'.1, hmem'.2, hna'⟩
  · rintro ⟨huz, huw', hzw', hna'⟩
    have hna : ¬Adjacent Pa u z := fun hcon => hna' (hF6_uz.mp hcon)
    have hex : ∃ S, DSeparatedPa Pa' {u} {z} S := by
      by_contra hc
      exact hna' ((adjacent_iff_forall_not_dSeparatedPa h' huz).mpr
        (fun Z hZ => hc ⟨Z, hZ⟩))
    obtain ⟨S, hS'⟩ := hex
    have hF5' := collider_iff_not_mem_of_dSeparatedPa h' (Or.inl huw' : Adjacent Pa' u w)
      (Or.inr hzw' : Adjacent Pa' w z) huz hS'
    have hwS : w ∉ S := hF5'.mp ⟨huw', hzw'⟩
    have hS : DSeparatedPa Pa {u} {z} S := (hds {u} {z} S).mpr hS'
    have hF5 := collider_iff_not_mem_of_dSeparatedPa h (hF6_uw.mpr (Or.inl huw'))
      (hF6_wz.mpr (Or.inr hzw')) huz hS
    have hmem : u ∈ Pa w ∧ z ∈ Pa w := hF5.mpr hwS
    exact ⟨huz, hmem.1, hmem.2, hna⟩

-- The assembled equivalence on structures (reverse: dSeparatedPa_iff_of_markovEquivalent).
/-- Verma-Pearl Theorem 1 (arXiv:1304.1108) on structures. -/
theorem markovEquivalent_iff_dSeparatedPa_iff {V : Type*} [DecidableEq V] [Finite V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (h' : IsAcyclic Pa') :
    ((∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w) ∧
        ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) ↔
      ∀ X Y Z, DSeparatedPa Pa X Y Z ↔ DSeparatedPa Pa' X Y Z := by
  constructor
  · rintro ⟨hskel, hv⟩ X Y Z
    exact dSeparatedPa_iff_of_markovEquivalent h h' hskel hv X Y Z
  · intro hds
    exact ⟨fun u w => adjacent_iff_of_dSeparatedPa_iff h h' hds u w,
      fun u w z => isVStructure_iff_of_dSeparatedPa_iff h h' hds u w z⟩

-- The same for networks, along a relabeling (reverse: BayesNet.dSeparated_iff_of_markovEquivalent)
/-- Verma-Pearl Theorem 1 (arXiv:1304.1108) for networks, along a relabeling. -/
theorem BayesNet.markovEquivalent_iff_dSeparated_iff {n : ℕ} (b : BayesNet α n)
    (b' : BayesNet β n) (e : Fin n ≃ Fin n) :
    ((∀ i j, b.Adj i j ↔ b'.Adj (e i) (e j)) ∧
        ∀ i j k, IsVStructure b.toPa i j k ↔ IsVStructure b'.toPa (e i) (e j) (e k)) ↔
      ∀ X Y Z, b.DSeparated X Y Z ↔ b'.DSeparated (e '' X) (e '' Y) (e '' Z) := by
  constructor
  · rintro ⟨hskel, hv⟩ X Y Z
    exact BayesNet.dSeparated_iff_of_markovEquivalent b b' e hskel hv X Y Z
  · intro hds
    have hds' : ∀ X Y Z : Set (Fin n),
        DSeparatedPa b.toPa X Y Z ↔ DSeparatedPa b'.toPa (e '' X) (e '' Y) (e '' Z) := by
      intro X Y Z
      exact (BayesNet.dSeparated_iff_dSeparatedPa_toPa b).symm.trans
        ((hds X Y Z).trans (BayesNet.dSeparated_iff_dSeparatedPa_toPa b'))
    have hacQ : IsAcyclic (relabel e b.toPa) := (isAcyclic_relabel e).mpr (isAcyclic_toPa b)
    have hac' : IsAcyclic b'.toPa := isAcyclic_toPa b'
    have hdQ : ∀ X Y Z : Set (Fin n),
        DSeparatedPa (relabel e b.toPa) X Y Z ↔ DSeparatedPa b'.toPa X Y Z := by
      intro X Y Z
      have heX : e '' (e.symm '' X) = X := by simp
      have heY : e '' (e.symm '' Y) = Y := by simp
      have heZ : e '' (e.symm '' Z) = Z := by simp
      have h1 : DSeparatedPa (relabel e b.toPa) (e '' (e.symm '' X)) (e '' (e.symm '' Y))
          (e '' (e.symm '' Z)) ↔
          DSeparatedPa b.toPa (e.symm '' X) (e.symm '' Y) (e.symm '' Z) :=
        dSeparatedPa_relabel e
      have h2 := hds' (e.symm '' X) (e.symm '' Y) (e.symm '' Z)
      rw [heX, heY, heZ] at h1 h2
      exact h1.trans h2
    obtain ⟨hskelQ, hvQ⟩ := (markovEquivalent_iff_dSeparatedPa_iff hacQ hac').mpr hdQ
    constructor
    · intro i j
      exact ((adjacent_toPa_iff b).symm.trans ((adjacent_relabel e i j).symm.trans
        ((hskelQ (e i) (e j)).trans (adjacent_toPa_iff b'))))
    · intro i j k
      exact ((isVStructure_relabel e i j k).symm.trans (hvQ (e i) (e j) (e k)))

end Cslib.MachineLearning.GraphicalModels
