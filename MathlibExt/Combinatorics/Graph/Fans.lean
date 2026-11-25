/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `07f64577` (PR #5949).
-/

module

public import MathlibExt.Combinatorics.Graph.MengerVertex
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

@[expose] public section

namespace MathlibExt.Combinatorics.Graph.Fans

open MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-! # Fans and the fan version of Menger's theorem

A `k`-fan from a vertex `a` to a set `B` is a family of `k` paths out of `a`
with distinct endpoints in `B`, pairwise meeting only at `a`.

We prove the fan version of Menger's theorem for `k`-connected graphs: every
vertex sends a `k`-fan to every set of at least `k` vertices not containing it.
The proof attaches a fresh sink vertex joined to `k` chosen targets and applies
the landed local vertex Menger theorem (`menger_vertex_max_min`); the
`k`-connectivity hypothesis forces every source-sink separator to have size at
least `k`, so truncating the resulting disjoint paths yields the fan. This
complements the landed global form `whitney_global_menger`, and together with
the easy direction (`fan_card_le_separator_card`)
shows every source-set separator has size at least `k`.
-/

/-- A `k`-fan from `a` to `B`: `k` paths out of `a` with distinct endpoints in
`B`, pairwise meeting only at `a`. -/
structure Fan {V : Type*} (G : SimpleGraph V) (a : V) (B : Set V) (k : ℕ) where
  endpoint : Fin k → V
  endpoint_mem : ∀ i, endpoint i ∈ B
  endpoint_injective : Function.Injective endpoint
  path : (i : Fin k) → G.Path a (endpoint i)
  disjoint : ∀ i j, i ≠ j → ∀ v ∈ (path i).val.support,
    v ∈ (path j).val.support → v = a

/-- `C` separates `a` from `B`: `a ∉ C`, and every walk from `a` to a vertex of
`B` meets `C`. -/
def SeparatesVertexFromSet {V : Type*} (G : SimpleGraph V) (a : V) (B : Set V)
    (C : Finset V) : Prop :=
  a ∉ C ∧ ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ C

/-- Easy direction of the fan min-max relation: a `k`-fan to `B` meets every
`a-B` separator in at least `k` vertices. -/
theorem fan_card_le_separator_card {V : Type*} (G : SimpleGraph V)
    {a : V} {B : Set V} {k : ℕ} (F : Fan G a B k) (C : Finset V)
    (hC : SeparatesVertexFromSet G a B C) : k ≤ C.card := by
  classical
  obtain ⟨haC, hhit⟩ := hC
  choose f hfmem hfC using
    (fun i => hhit (F.endpoint i) (F.endpoint_mem i) (F.path i).val)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hmem : f i ∈ (F.path j).val.support := by rw [hij]; exact hfmem j
    have h := F.disjoint i j hne (f i) (hfmem i) hmem
    exact haC (h ▸ hfC i)
  have hcard : (Finset.image f Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : Finset.image f Finset.univ ⊆ C := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfC i
  calc k = (Finset.image f Finset.univ).card := hcard.symm
    _ ≤ C.card := Finset.card_le_card hsub

/-- Adjacency of the sink-augmented graph on `Option V`: old edges between
`some`-vertices, and the fresh sink `none` joined exactly to `T`. -/
private def sinkAdj {V : Type*} (G : SimpleGraph V) (T : Finset V) :
    Option V → Option V → Prop
  | some u, some v => G.Adj u v
  | some u, none => u ∈ T
  | none, some v => v ∈ T
  | none, none => False

private theorem sinkAdj_symm {V : Type*} (G : SimpleGraph V) (T : Finset V) :
    Std.Symm (sinkAdj G T) where
  symm x y h := by
    cases x with
    | none =>
        cases y with
        | none => exact h
        | some v => exact h
    | some u =>
        cases y with
        | none => exact h
        | some v => exact G.adj_symm h

private theorem sinkAdj_irrefl {V : Type*} (G : SimpleGraph V) (T : Finset V) :
    Std.Irrefl (sinkAdj G T) where
  irrefl x h := by
    cases x with
    | none => exact h
    | some u => exact G.irrefl h

/-- The sink-augmented graph: `G` on the `some`-vertices plus a fresh sink
`none` joined exactly to `T`. -/
private def sinkGraph {V : Type*} (G : SimpleGraph V) (T : Finset V) :
    SimpleGraph (Option V) where
  Adj := sinkAdj G T
  symm := sinkAdj_symm G T
  loopless := sinkAdj_irrefl G T

/-- A `G`-walk ending in `T` extends to a sink-graph walk ending at the sink,
appending the final sink edge. -/
private noncomputable def walkToSinkSnoc {V : Type*} (G : SimpleGraph V)
    (T : Finset V) {u v : V} (w : G.Walk u v) :
    v ∈ T →
      { p : (sinkGraph G T).Walk (some u) none //
        p.support = w.support.map some ++ [none] } := by
  induction w with
  | nil =>
      rename_i u
      intro hv
      have h' : (sinkGraph G T).Adj (some u) none := hv
      refine ⟨SimpleGraph.Walk.cons h' SimpleGraph.Walk.nil, ?_⟩
      simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
  | @cons a b c hab tail ih =>
      intro hv
      obtain ⟨p', hp'⟩ := ih hv
      have h' : (sinkGraph G T).Adj (some a) (some b) := hab
      refine ⟨SimpleGraph.Walk.cons h' p', ?_⟩
      simp [SimpleGraph.Walk.support_cons, hp']

/-- A sink-graph walk ending at the sink splits off a final sink edge: it
contains a walk from the same start to a vertex of `T` that avoids the sink,
stays inside the original support, and keeps a duplicate-free support. -/
private theorem decomp_sink_walk {V : Type*} (G : SimpleGraph V) (T : Finset V)
    {x y : Option V} (q : (sinkGraph G T).Walk x y) :
    y = none → q.support.Nodup → x ≠ none →
    ∃ (t : V) (_ : t ∈ T) (q' : (sinkGraph G T).Walk x (some t)),
      (∀ v ∈ q'.support, v ≠ none) ∧
        (∀ v ∈ q'.support, v ∈ q.support) ∧ q'.support.Nodup := by
  induction q with
  | nil =>
      intro hy _ hx
      exact absurd hy hx
  | @cons a b c hab tail ih =>
      intro hy hnodup hx
      subst hy
      rw [SimpleGraph.Walk.support_cons] at hnodup
      cases b with
      | none =>
          cases a with
          | none => exact absurd rfl hx
          | some s =>
              refine ⟨s, hab, SimpleGraph.Walk.nil, ?_, ?_, ?_⟩
              · intro v hv
                simp only [SimpleGraph.Walk.support_nil,
                  List.mem_singleton] at hv
                subst hv
                simp
              · intro v hv
                simp only [SimpleGraph.Walk.support_nil,
                  List.mem_singleton] at hv
                subst hv
                simp
              · simp [SimpleGraph.Walk.support_nil]
      | some b' =>
          have htail_nodup : tail.support.Nodup :=
            (List.nodup_cons.mp hnodup).2
          obtain ⟨t, ht, q', hnone, hsub, hn'⟩ :=
            ih rfl htail_nodup (by simp)
          refine ⟨t, ht, SimpleGraph.Walk.cons hab q', ?_, ?_, ?_⟩
          · intro v hv
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
            rcases hv with rfl | hv
            · exact hx
            · exact hnone v hv
          · intro v hv
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
            rcases hv with rfl | hv
            · rw [SimpleGraph.Walk.support_cons, List.mem_cons]
              exact Or.inl rfl
            · rw [SimpleGraph.Walk.support_cons, List.mem_cons]
              exact Or.inr (hsub v hv)
          · rw [SimpleGraph.Walk.support_cons, List.nodup_cons]
            refine ⟨?_, hn'⟩
            intro hcon
            exact (List.nodup_cons.mp hnodup).1 (hsub a hcon)

/-- A sink-graph walk avoiding the sink projects to a `G`-walk with the
`getD`-mapped support. -/
private noncomputable def walkOfSink {V : Type*} (G : SimpleGraph V)
    (T : Finset V) (d : V) {x y : Option V} (q : (sinkGraph G T).Walk x y) :
    (∀ v ∈ q.support, v ≠ none) →
    { p : G.Walk (Option.getD x d) (Option.getD y d) //
      p.support = q.support.map (fun z => Option.getD z d) } := by
  induction q with
  | nil =>
      intro _
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      simp [SimpleGraph.Walk.support_nil]
  | @cons a b c hab tail ih =>
      intro hall
      rw [SimpleGraph.Walk.support_cons] at hall
      have ha : a ≠ none := hall a List.mem_cons_self
      have hb : b ≠ none :=
        hall b (List.mem_cons_of_mem _ tail.start_mem_support)
      cases a with
      | none => exact absurd rfl ha
      | some a' =>
          cases b with
          | none => exact absurd rfl hb
          | some b' =>
              obtain ⟨p', hp'⟩ :=
                ih (fun v hv => hall v (List.mem_cons_of_mem _ hv))
              have hab' : G.Adj (Option.getD (some a') d)
                  (Option.getD (some b') d) := hab
              refine ⟨SimpleGraph.Walk.cons hab' p', ?_⟩
              simp only [SimpleGraph.Walk.support_cons, hp',
                show ((some a' :: tail.support).map fun z => Option.getD z d) =
                  (Option.getD (some a') d) ::
                    (tail.support.map fun z => Option.getD z d) from rfl]

/-- Mapping a duplicate-free `none`-free list through `getD` keeps it
duplicate-free. -/
private theorem nodup_map_getD_of_none_free {V : Type*} {d : V}
    {l : List (Option V)} :
    l.Nodup → (∀ v ∈ l, v ≠ none) →
      (l.map fun z => Option.getD z d).Nodup := by
  induction l with
  | nil =>
      intro _ _
      exact List.nodup_nil
  | cons x xs ih =>
      intro hnodup hall
      have hx : x ≠ none := hall x List.mem_cons_self
      have hxs : ∀ v ∈ xs, v ≠ none :=
        fun v hv => hall v (List.mem_cons_of_mem _ hv)
      have hnodup' : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hxmem : x ∉ xs := (List.nodup_cons.mp hnodup).1
      rw [show ((x :: xs).map fun z => Option.getD z d) =
        (Option.getD x d) :: (xs.map fun z => Option.getD z d) from rfl,
        List.nodup_cons]
      refine ⟨?_, ih hnodup' hxs⟩
      intro hcon
      obtain ⟨y, hymem, hyeq⟩ := List.mem_map.mp hcon
      cases x with
      | none => exact absurd rfl hx
      | some x' =>
          cases y with
          | none => exact (hxs _ hymem) rfl
          | some y' =>
              have hyeq' : y' = x' := hyeq
              subst hyeq'
              exact hxmem hymem

/-- A walk in an induced subgraph projects to a walk in the ambient graph whose
support lies in the inducing set. -/
private theorem induceWalk_to_walk {V : Type*} (G : SimpleGraph V) (S : Set V)
    {a b : S} (q : (G.induce S).Walk a b) :
    ∃ w : G.Walk a.val b.val, ∀ v ∈ w.support, v ∈ S := by
  induction q with
  | nil =>
      rename_i u
      refine ⟨SimpleGraph.Walk.nil, fun v hv => ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv
      exact u.property
  | @cons x y _ h q ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨SimpleGraph.Walk.cons (SimpleGraph.induce_adj.mp h) w,
        fun v hv => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact x.property
      · exact hw v hv

/-- One leg of the fan under construction: an endpoint in `T` with a `G`-walk
from `a` whose vertices lie on the corresponding Menger path. -/
private structure FanLeg {V : Type*} (G : SimpleGraph V) (a : V) (T : Finset V)
    {n : ℕ} (paths : Fin n → (sinkGraph G T).Path (some a) none)
    {k : ℕ} (hkn : k ≤ n) (i : Fin k) where
  endpoint : V
  endpoint_mem : endpoint ∈ T
  walk : G.Walk a endpoint
  walk_nodup : walk.support.Nodup
  walk_mem : ∀ v ∈ walk.support,
    some v ∈ (paths ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩).val.support

/-- Fan version of Menger's theorem for `k`-connected graphs: every vertex `a`
sends a `k`-fan to every set `B` of at least `k` vertices not containing `a`. -/
theorem exists_fan_of_isVertexConnected {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsVertexConnected k) (a : V) (B : Finset V) (ha : a ∉ B)
    (hB : k ≤ B.card) :
    Nonempty (Fan G a (↑B) k) := by
  classical
  obtain ⟨T, hTB, hTcard⟩ := Finset.exists_subset_card_eq hB
  have haT : a ∉ T := fun hcon => ha (hTB hcon)
  have hst : (some a : Option V) ≠ none := by simp
  have hadj : ¬ (sinkGraph G T).Adj (some a) none := haT
  obtain ⟨n, paths, C, hdisj, hcut, hcard, -, -⟩ :=
    menger_vertex_max_min (G := sinkGraph G T) (some a) none hst hadj
  have hkn : k ≤ n := by
    have hle : k ≤ C.card := by
      by_contra hlt
      rw [not_le] at hlt
      have himg : (T.image some).card = k := by
        rw [Finset.card_image_of_injective _
          (fun _ _ h => Option.some_inj.mp h), hTcard]
      have hnotsub : ¬ T.image some ⊆ C := by
        intro hsub
        have hle2 := Finset.card_le_card hsub
        omega
      obtain ⟨x, hximg, hxC⟩ := Finset.not_subset.mp hnotsub
      obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp hximg
      obtain ⟨hsC, hzC, hhit⟩ :=
        (isSTVertexCut_iff_walkSeparator (sinkGraph G T) (some a) none C).mp
          hcut
      have hC₀mem : ∀ v : V,
          v ∈ Finset.univ.filter (fun v => some v ∈ C) ↔ some v ∈ C := by
        intro v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hC₀card :
          (Finset.univ.filter (fun v => some v ∈ C)).card ≤ C.card := by
        have hsub : (Finset.univ.filter (fun v => some v ∈ C)).image some ⊆ C := by
          intro y hy
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
          exact (hC₀mem v).mp hv
        have hle3 := Finset.card_le_card hsub
        rwa [Finset.card_image_of_injective _
          (fun _ _ h => Option.some_inj.mp h)] at hle3
      have haC₀ : a ∉ Finset.univ.filter (fun v => some v ∈ C) :=
        fun h => hsC ((hC₀mem a).mp h)
      have htC₀ : t ∉ Finset.univ.filter (fun v => some v ∈ C) :=
        fun h => hxC ((hC₀mem t).mp h)
      have hC₀lt : (Finset.univ.filter (fun v => some v ∈ C)).card < k := by
        omega
      have hconn := hG.2 _ hC₀lt
      have hsS : a ∈ ((Finset.univ.filter (fun v => some v ∈ C) :
          Finset V) : Set V)ᶜ :=
        (Set.mem_compl_iff _ _).mpr (fun h2 => haC₀ (Finset.mem_coe.mp h2))
      have htS : t ∈ ((Finset.univ.filter (fun v => some v ∈ C) :
          Finset V) : Set V)ᶜ :=
        (Set.mem_compl_iff _ _).mpr (fun h2 => htC₀ (Finset.mem_coe.mp h2))
      obtain ⟨q⟩ := hconn ⟨a, hsS⟩ ⟨t, htS⟩
      obtain ⟨w, hw⟩ := induceWalk_to_walk G _ q
      have hwC₀ : ∀ v ∈ w.support,
          v ∉ Finset.univ.filter (fun v => some v ∈ C) := by
        intro v hv hcon
        exact (Set.mem_compl_iff _ _).mp (hw v hv) (Finset.mem_coe.mpr hcon)
      obtain ⟨p, hp⟩ := walkToSinkSnoc G T w htT
      obtain ⟨y, hy, hyC⟩ := hhit p
      rw [hp, List.mem_append] at hy
      rcases hy with hy | hy
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
        exact hwC₀ v hv ((hC₀mem v).mpr hyC)
      · simp only [List.mem_singleton] at hy
        subst hy
        exact hzC hyC
    omega
  have hidx : ∀ {i j : Fin k}, i ≠ j →
      (⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ : Fin n) ≠
        ⟨j.val, lt_of_lt_of_le j.isLt hkn⟩ := by
    intro i j hne hcon
    have h2 := congrArg Fin.val hcon
    have hval : i.val = j.val := h2
    exact hne (Fin.ext hval)
  have hex : ∀ i : Fin k, ∃ _ : FanLeg G a T paths hkn i, True := by
    intro i
    have hnodup :=
      (paths ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩).property.support_nodup
    obtain ⟨t, ht, q', hnone, hsub, hq'nodup⟩ :=
      decomp_sink_walk G T _ rfl hnodup (by simp)
    obtain ⟨Q, hQsup⟩ := walkOfSink G T a q' hnone
    refine ⟨⟨t, ht, Q, ?_, ?_⟩, trivial⟩
    · rw [hQsup]
      exact nodup_map_getD_of_none_free hq'nodup hnone
    · intro v hv
      rw [hQsup] at hv
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hv
      have hxne := hnone x hx
      cases x with
      | none => exact absurd rfl hxne
      | some w =>
          have hxeq' : w = v := hxeq
          subst hxeq'
          exact hsub _ hx
  choose hleg _htrue using hex
  refine ⟨Fan.mk (fun i => (hleg i).endpoint)
    (fun i => Finset.mem_coe.mpr (hTB (hleg i).endpoint_mem)) ?_ ?_ ?_⟩
  · intro i j hij
    have hij' : (hleg i).endpoint = (hleg j).endpoint := hij
    by_contra hne
    have hmemI : some (hleg i).endpoint ∈
        (paths ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩).val.support :=
      (hleg i).walk_mem _ (hleg i).walk.end_mem_support
    have hmemJ : some (hleg i).endpoint ∈
        (paths ⟨j.val, lt_of_lt_of_le j.isLt hkn⟩).val.support := by
      rw [hij']
      exact (hleg j).walk_mem _ (hleg j).walk.end_mem_support
    rcases hdisj _ _ (hidx hne) _ hmemI hmemJ with h | h
    · have heq : (hleg i).endpoint = a := Option.some_inj.mp h
      have hmem := (hleg i).endpoint_mem
      rw [heq] at hmem
      exact haT hmem
    · simp at h
  · exact fun i => ⟨(hleg i).walk,
      SimpleGraph.Walk.IsPath.mk' (hleg i).walk_nodup⟩
  · intro i j hne v hvi hvj
    have hmemI : some v ∈
        (paths ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩).val.support :=
      (hleg i).walk_mem v hvi
    have hmemJ : some v ∈
        (paths ⟨j.val, lt_of_lt_of_le j.isLt hkn⟩).val.support :=
      (hleg j).walk_mem v hvj
    rcases hdisj _ _ (hidx hne) _ hmemI hmemJ with h | h
    · exact Option.some_inj.mp h
    · simp at h

/-- In a `k`-connected graph, every separator of `a` from `B` has size at least
`k` when `a ∉ B` and `B` has at least `k` vertices. -/
theorem separator_card_ge_of_isVertexConnected {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsVertexConnected k) (a : V) (B : Finset V) (ha : a ∉ B)
    (hB : k ≤ B.card) (C : Finset V)
    (hC : SeparatesVertexFromSet G a (↑B) C) : k ≤ C.card := by
  obtain ⟨F⟩ := exists_fan_of_isVertexConnected hG a B ha hB
  exact fan_card_le_separator_card G F C hC

end MathlibExt.Combinatorics.Graph.Fans
