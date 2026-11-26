/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RationalSimplicialHomologyShared
import Mathlib.Data.List.Sublists
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

/-!
# A non-partitionable Cohen–Macaulay simplicial complex

The three-copy complex of Duval, Goeckner, Klivans and Martin refutes the Stanley–Garsia
partitionability conjecture. We verify Reisner's criterion over the rationals by sparse column
elimination and rule out facet intervals on the faces used in their combinatorial obstruction.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/CohenMacaulayPartitionabilityAMR156Problem0005Wanted.lean`:

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 6 (Stanley–Garsia partitionability conjecture). UnsolvedMath record UM-00801179
(`AMR-156-0005`), dataset ulamai/UnsolvedMath v1.8.0.

Finite abstract simplicial complexes on the vertex set `ℕ`, links and reduced rational Betti numbers
are those of `MathlibExt/Combinatorics/RationalSimplicialHomologyShared.lean`. Cohen–Macaulay over
`ℚ` is Reisner's criterion: `H̃_i(link F; ℚ) = 0` for `i < dim link F` (degrees above the dimension
vanish automatically). Partitionable: the faces are partitioned into intervals `[r F, F]` indexed by
the facets. Duval–Goeckner–Klivans–Martin take Reisner's criterion over an arbitrary field;
Cohen–Macaulayness over any field implies it over `ℚ` (universal coefficients: vanishing mod `p`
forces the integral homology to be finite), and their complexes are built from shellable balls.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

/-- **Cohen–Macaulay complexes over $\mathbb{Q}$.** A finite family $K$ of finite subsets of
$\mathbb{N}$ is Cohen–Macaulay over $\mathbb{Q}$ when for every member $F$ of $K$ (the empty face
included, if it belongs to $K$) the link
$L = \operatorname{lk}_K F = \{G \in K : G \cap F = \emptyset,\ G \cup F \in K\}$ satisfies
$\tilde\beta_i(L) = 0$ for every integer $i$ with $-1 \le i < \dim L$. Here $\dim L$ is one less
than the largest number of elements of a member of $L$, taken to be $-1$ when $L$ has no nonempty
member, and $\tilde\beta_i(L)$ is the number of members of $L$ with $i + 1$ elements minus the
ranks of the augmented rational simplicial boundary maps (vertices ordered as in $\mathbb{N}$) out
of and into the span of these members; when $L$ is a simplicial complex,
$\tilde\beta_i(L) = \dim \tilde H_i(L; \mathbb{Q})$.

For a simplicial complex this is Reisner's criterion. -/
def IsCohenMacaulayOverRat (K : Finset (Finset ℕ)) : Prop :=
  ∀ F ∈ K, ∀ k, k < topCard (link K F) → reducedBetti (link K F) k = 0

/-- **Pure complexes.** A finite family $K$ of finite subsets of $\mathbb{N}$ is pure when all
its facets (maximal members) have the same number of elements. -/
def IsPure (K : Finset (Finset ℕ)) : Prop :=
  ∃ d : ℕ, ∀ F, IsFacet K F → F.card = d

/-- **Partitionable complexes.** A finite family $K$ of finite subsets of $\mathbb{N}$ is
partitionable when there is a map $r$ assigning to each facet $F$ of $K$ a set $r(F) \subseteq F$
such that for every member $\sigma$ of $K$ there is exactly one facet $F$ of $K$ with
$r(F) \subseteq \sigma \subseteq F$.

For a simplicial complex this says that its faces are partitioned into the intervals
$[r(F), F] = \{\sigma : r(F) \subseteq \sigma \subseteq F\}$, one for each facet $F$. -/
def IsPartitionable (K : Finset (Finset ℕ)) : Prop :=
  ∃ r : Finset ℕ → Finset ℕ, (∀ F, IsFacet K F → r F ⊆ F) ∧
    ∀ σ ∈ K, ∃! F, IsFacet K F ∧ r F ⊆ σ ∧ σ ⊆ F

/-- **Stanley–Garsia partitionability conjecture.** Every finite simplicial complex on the vertex
set $\mathbb{N}$ that is pure and Cohen–Macaulay over $\mathbb{Q}$ is partitionable.

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 6
(partitionability conjecture of Stanley and Garsia). -/
def cohenMacaulayPartitionable : Prop :=
  ∀ K : Finset (Finset ℕ), IsSimplicialComplex K → IsPure K → IsCohenMacaulayOverRat K →
    IsPartitionable K

open Submodule
variable {α : Type} [DecidableEq α]

private abbrev Chain (α : Type) := List (α × ℚ)

private def coeff (v : Chain α) (i : α) : ℚ :=
  (v.map fun t => if t.1 = i then t.2 else 0).sum

private theorem coeff_cons (a i : α) (c : ℚ) (v : Chain α) :
    coeff ((a, c) :: v) i = (if a = i then c else 0) + coeff v i := by simp [coeff]

-- Combine like terms and drop zeros to keep the columns sparse during elimination.
private def addTerm (a : α) (c : ℚ) : Chain α → Chain α
  | [] => if c = 0 then [] else [(a, c)]
  | (b, d) :: v =>
    if a = b then (if c + d = 0 then v else (a, c + d) :: v)
    else (b, d) :: addTerm a c v

private theorem coeff_addTerm (a i : α) (c : ℚ) (v : Chain α) :
    coeff (addTerm a c v) i = (if a = i then c else 0) + coeff v i := by
  induction v with
  | nil => by_cases hc : c = 0 <;> simp [addTerm, coeff, hc]
  | cons t v ih =>
    obtain ⟨b, d⟩ := t
    by_cases hab : a = b
    · subst b
      by_cases h : c + d = 0 <;> by_cases hi : a = i <;>
        simp [addTerm, coeff_cons, h, hi, ← add_assoc]
    · simp [addTerm, hab, coeff_cons, ih, add_left_comm]

private def addScaled (c : ℚ) (v w : Chain α) : Chain α :=
  v.foldr (fun t acc => addTerm t.1 (c * t.2) acc) w

private theorem coeff_addScaled (c : ℚ) (v w : Chain α) :
    coeff (addScaled c v w) = c • coeff v + coeff w := by
  ext i
  induction v with
  | nil => simp [addScaled, coeff]
  | cons t v ih =>
    obtain ⟨a, b⟩ := t
    change coeff (addTerm a (c * b) (addScaled c v w)) i = _
    rw [coeff_addTerm, ih]
    by_cases h : a = i <;> simp [h, coeff_cons, mul_add, add_assoc]

private def clearAt (a : α) (v w : Chain α) : Chain α :=
  if coeff w a = 0 then w else addScaled (-(coeff w a / coeff v a)) v w

private theorem coeff_clearAt (a : α) (v w : Chain α) :
    coeff (clearAt a v w) = -(coeff w a / coeff v a) • coeff v + coeff w := by
  unfold clearAt
  split <;> rename_i h
  · simp [h]
  · exact coeff_addScaled ..

private def chainSpan (vs : List (Chain α)) : Submodule ℚ (α → ℚ) :=
  span ℚ (coeff '' {v | v ∈ vs})

private theorem mem_chainSpan {w : Chain α} {vs : List (Chain α)} (hw : w ∈ vs) :
    coeff w ∈ chainSpan vs := subset_span ⟨w, hw, rfl⟩

private theorem chainSpan_cons (v : Chain α) (vs : List (Chain α)) :
    chainSpan (v :: vs) = ℚ ∙ coeff v ⊔ chainSpan vs := by
  simp [chainSpan, Set.ofPred_or, List.mem_cons, span_insert]

private theorem chainSpan_nil : chainSpan ([] : List (Chain α)) = ⊥ := by
  simp [chainSpan]

private instance chainSpan_finite (vs : List (Chain α)) : Module.Finite ℚ (chainSpan vs) :=
  Module.Finite.span_of_finite _ (vs.finite_toSet.image coeff)

-- Clearing the pivot coordinate puts the remaining columns in a hyperplane complementary
-- to the pivot line. A zero column leaves the span unchanged.
private def columnRank : ℕ → List (Chain α) → ℕ
  | 0, _ | _, [] => 0
  | n + 1, v :: vs =>
    match v.find? (fun t => coeff v t.1 != 0) with
    | none => columnRank n vs
    | some t => columnRank n (vs.map (clearAt t.1 v)) + 1

private theorem columnRank_eq (n : ℕ) (vs : List (Chain α)) (hlen : vs.length ≤ n) :
    columnRank n vs = Module.finrank ℚ (chainSpan vs) := by
  induction n generalizing vs with
  | zero =>
    have : vs = [] := List.length_eq_zero_iff.mp (by omega)
    subst vs
    rw [columnRank, chainSpan_nil, finrank_bot]
  | succ n ih =>
    cases vs with
    | nil =>
      change 0 = _
      rw [chainSpan_nil, finrank_bot]
    | cons v vs =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      rw [columnRank]
      split
      · rename_i h
        have hz : coeff v = 0 := by
          ext i
          by_cases hi : ∃ t ∈ v, t.1 = i
          · obtain ⟨t, ht, rfl⟩ := hi
            simpa using List.find?_eq_none.mp h t ht
          · apply List.sum_eq_zero
            intro x hx
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
            simp [show t.1 ≠ i from fun he => hi ⟨t, ht, he⟩]
        rw [chainSpan_cons, hz, span_zero_singleton, bot_sup_eq]
        exact ih vs hlen
      · rename_i t ht
        let a := t.1
        have ha : coeff v a ≠ 0 := by simpa [a] using List.find?_some ht
        let S := chainSpan (vs.map (clearAt a v))
        let P := ℚ ∙ coeff v
        have hv : coeff v ∈ P := mem_span_singleton_self _
        have heq : chainSpan (v :: vs) = P ⊔ S := by
          apply le_antisymm
          · apply span_le.mpr
            rintro _ ⟨w, hw, rfl⟩
            rcases List.mem_cons.mp hw with rfl | hw
            · exact (show P ≤ P ⊔ S from le_sup_left) hv
            have hw' : coeff (clearAt a v w) ∈ P ⊔ S :=
              (show S ≤ P ⊔ S from le_sup_right) (mem_chainSpan (List.mem_map_of_mem hw))
            rw [coeff_clearAt] at hw'
            have hp : coeff v ∈ P ⊔ S := (show P ≤ P ⊔ S from le_sup_left) hv
            exact (Submodule.add_mem_iff_right _ (Submodule.smul_mem _ _ hp)).mp hw'
          · apply sup_le
            · rw [chainSpan_cons]
              exact le_sup_left
            apply span_le.mpr
            rintro _ ⟨w, hw, rfl⟩
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
            rw [coeff_clearAt]
            exact add_mem (smul_mem _ _ (mem_chainSpan List.mem_cons_self))
              (mem_chainSpan (List.mem_cons_of_mem _ hu))
        have hker : S ≤ LinearMap.ker (LinearMap.proj a : (α → ℚ) →ₗ[ℚ] ℚ) := by
          apply span_le.mpr
          rintro _ ⟨w, hw, rfl⟩
          obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
          simp [LinearMap.mem_ker, coeff_clearAt, ha]
        have hdis : Disjoint P S := by
          rw [Submodule.disjoint_def]
          intro x hx hx'
          obtain ⟨c, rfl⟩ := mem_span_singleton.mp hx
          have hc := hker hx'
          simp [LinearMap.mem_ker, ha] at hc
          simp [hc]
        have hv0 : coeff v ≠ 0 := fun h => ha (by simp [h])
        have hdim := Submodule.finrank_sup_add_finrank_inf_eq P S
        rw [hdis.eq_bot, finrank_bot, add_zero] at hdim
        rw [ih _ (by simpa using hlen), heq, hdim]
        change Module.finrank ℚ S + 1 = Module.finrank ℚ (ℚ ∙ coeff v) + _
        rw [finrank_span_singleton hv0, add_comm]

private abbrev Face := Finset ℕ

-- Facets from equation (5) of Duval et al. The three copies share precisely the vertices
-- other than 1, 5, and 9.
private def facetsX : List (List ℕ) :=
  [[1, 2, 4, 9], [1, 2, 6, 9], [1, 5, 6, 9], [1, 5, 8, 9], [1, 4, 8, 9],
   [1, 4, 5, 8], [1, 4, 5, 7], [4, 5, 7, 8], [1, 2, 5, 6], [0, 1, 2, 5],
   [0, 2, 5, 6], [0, 1, 2, 3], [1, 2, 3, 4], [1, 3, 4, 7]]

private def copyVertex (j : ℕ) : ℕ → ℕ
  | 1 => if j = 0 then 1 else 7 + 3 * j
  | 5 => if j = 0 then 5 else 8 + 3 * j
  | 9 => if j = 0 then 9 else 9 + 3 * j
  | i => i

private def facetsC : List (List ℕ) :=
  (List.range 3).flatMap fun j => facetsX.map (List.map (copyVertex j))

private def facesC : List Face :=
  (facetsC.flatMap fun t => t.sublists.map List.toFinset).dedup

private def linkFaces (F : Face) : List Face :=
  ((facesC.filter fun t => F ⊆ t).map fun t => t \ F)

private def vertices (σ : Face) : List ℕ :=
  (List.range (σ.sup id + 1)).filter (· ∈ σ)

private theorem vertices_toFinset (σ : Face) : (vertices σ).toFinset = σ := by
  ext i
  simp only [vertices, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact and_iff_right_of_imp fun h => Nat.lt_succ_of_le (Finset.le_sup (f := id) h)

private def boundary (σ : Face) : Chain Face :=
  (vertices σ).map fun v => (σ.erase v, (-1) ^ (σ.filter (· < v)).card)

private def boundaryRank (fs : List Face) (k : ℕ) : ℕ :=
  let cols := (fs.filter fun σ => σ.card = k + 1).map boundary
  columnRank cols.length cols

private theorem coeff_boundary (σ τ : Face) :
    coeff (boundary σ) τ =
      ∑ v ∈ σ, if σ.erase v = τ then (-1) ^ (σ.filter (· < v)).card else 0 := by
  simpa [coeff, boundary, List.map_map, Function.comp_def, vertices_toFinset] using
    (List.sum_toFinset (fun v => if σ.erase v = τ then (-1 : ℚ) ^ (σ.filter (· < v)).card
      else 0) (show (vertices σ).Nodup from List.Nodup.filter _ List.nodup_range)).symm

-- Extend each column by zero from its row index set to all finite vertex sets.
-- This embeds the column span and identifies its generators with the sparse boundaries.
private theorem boundaryRank_eq (fs : List Face) (K : Finset Face) (k : ℕ)
    (hfs : fs.toFinset = K) (hc : IsSimplicialComplex K) :
    boundaryRank fs k = (boundaryMatrix K k).rank := by
  let rows := facesOfCard K k
  let cols := facesOfCard K (k + 1)
  let A := boundaryMatrix K k
  let e : (rows → ℚ) →ₗ[ℚ] (Face → ℚ) := LinearMap.pi fun i =>
    if h : i ∈ rows then LinearMap.proj (⟨i, h⟩ : rows) else 0
  have hinj : Function.Injective e := by
    intro u v h
    funext i
    simpa [e, i.property] using congrFun h i.val
  have he (σ : cols) : e (A.col σ) = coeff (boundary σ.val) := by
    ext τ
    rw [coeff_boundary]
    by_cases hτ : τ ∈ rows
    · simp [e, hτ, A, Matrix.col, boundaryMatrix]
    simp only [e, LinearMap.pi_apply, dite_eq_right hτ, LinearMap.zero_apply]
    symm
    apply Finset.sum_eq_zero
    intro v hv
    have hσ := Finset.mem_filter.mp σ.property
    have hne : σ.val.erase v ≠ τ := by
      rintro rfl
      exact hτ (Finset.mem_filter.mpr ⟨hc _ hσ.1 _ (Finset.erase_subset _ _),
        by rw [Finset.card_erase_of_mem hv, hσ.2, Nat.add_sub_cancel]⟩)
    simp [hne]
  rw [boundaryRank, columnRank_eq _ _ le_rfl, Matrix.rank_eq_finrank_span_cols]
  change _ = Module.finrank ℚ (span ℚ (Set.range A.col))
  rw [(Submodule.equivMapOfInjective e hinj (span ℚ (Set.range A.col))).finrank_eq]
  apply congrArg (fun S : Submodule ℚ (Face → ℚ) => Module.finrank ℚ S)
  rw [Submodule.map_span]
  unfold chainSpan
  apply congrArg (span ℚ)
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hm, hd⟩ := List.mem_filter.mp hσ
    have hm' : σ ∈ K := hfs ▸ (List.mem_toFinset.mpr hm)
    let c : cols := ⟨σ, Finset.mem_filter.mpr ⟨hm', by simpa using hd⟩⟩
    exact ⟨_, ⟨c, rfl⟩, he c⟩
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    have hσ := Finset.mem_filter.mp σ.property
    have hm : σ.val ∈ fs := List.mem_toFinset.mp (hfs.symm ▸ hσ.1)
    exact ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, by simp [hσ.2]⟩), (he σ).symm⟩

private def complexC := facesC.toFinset

private theorem mem_complexC {σ : Face} :
    σ ∈ complexC ↔ ∃ t ∈ facetsC, σ ⊆ t.toFinset := by
  simp only [complexC, facesC, List.mem_toFinset, List.mem_dedup, List.mem_flatMap,
    List.mem_map, List.mem_sublists]
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    exact ⟨t, ht, fun x hx => List.mem_toFinset.mpr (hu.subset (List.mem_toFinset.mp hx))⟩
  · rintro ⟨t, ht, hσ⟩
    refine ⟨t, ht, t.filter (· ∈ σ), List.filter_sublist, ?_⟩
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact and_iff_right_of_imp fun h => List.mem_toFinset.mp (hσ h)

private theorem complexC_simplicial : IsSimplicialComplex complexC := by
  intro σ hσ τ hτ
  obtain ⟨t, ht, hs⟩ := mem_complexC.mp hσ
  exact mem_complexC.mpr ⟨t, ht, hτ.trans hs⟩

private theorem facet_list {F : Face} (h : IsFacet complexC F) :
    ∃ t ∈ facetsC, t.toFinset = F := by
  obtain ⟨t, ht, hs⟩ := mem_complexC.mp h.1
  exact ⟨t, ht, h.2 _ (mem_complexC.mpr ⟨t, ht, Finset.Subset.rfl⟩) hs⟩

private theorem complexC_pure : IsPure complexC := by
  refine ⟨4, fun F hF => ?_⟩
  obtain ⟨t, ht, rfl⟩ := facet_list hF
  exact (show ∀ f ∈ facetsC, f.toFinset.card = 4 by decide) t ht

private theorem linkFaces_eq (F : Face) : (linkFaces F).toFinset = link complexC F := by
  ext σ
  simp only [linkFaces, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq,
    link, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hF⟩, rfl⟩
    have ht' : t ∈ complexC := List.mem_toFinset.mpr ht
    exact ⟨complexC_simplicial _ ht' _ Finset.sdiff_subset, Finset.sdiff_disjoint,
      (Finset.sdiff_union_of_subset hF).symm ▸ ht'⟩
  · rintro ⟨_, hd, h⟩
    exact ⟨σ ∪ F, ⟨List.mem_toFinset.mp h, Finset.subset_union_right⟩,
      Finset.union_sdiff_cancel_right hd⟩

private theorem link_simplicial (F : Face) : IsSimplicialComplex (link complexC F) := by
  intro σ hσ τ ht
  obtain ⟨h, hd, hu⟩ := Finset.mem_filter.mp hσ
  exact Finset.mem_filter.mpr ⟨complexC_simplicial _ h _ ht, hd.mono_left ht,
    complexC_simplicial _ hu _ (Finset.union_subset_union ht Finset.Subset.rfl)⟩

private def linkCheck (fs : List Face) : Bool :=
  (List.range (topCard fs.toFinset)).all fun k =>
    (facesOfCard fs.toFinset k).card ==
      (if k = 0 then 0 else boundaryRank fs (k - 1)) + boundaryRank fs k

private theorem linkCheck_sound (F : Face) (h : linkCheck (linkFaces F)) :
    ∀ k, k < topCard (link complexC F) → reducedBetti (link complexC F) k = 0 := by
  intro k hk
  have he := List.all_eq_true.mp h k (List.mem_range.mpr (by rwa [linkFaces_eq]))
  simp only [beq_iff_eq, linkFaces_eq] at he
  have hr (j : ℕ) := boundaryRank_eq (linkFaces F) _ j (linkFaces_eq F) (link_simplicial F)
  by_cases hk0 : k = 0
  · subst k
    simp only [ite_true, zero_add, hr] at he
    simp only [reducedBetti, ite_true, sub_zero, he, sub_self]
  · simp only [ite_eq_right hk0, hr] at he
    simp only [reducedBetti, ite_eq_right hk0, he, Nat.cast_add]
    ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
-- Check the sparse boundary ranks for each of the 228 face links.
private theorem complexC_cm : IsCohenMacaulayOverRat complexC := by
  have h : facesC.all (fun F => linkCheck (linkFaces F)) = true := by decide +kernel
  intro F hF
  exact linkCheck_sound F (List.all_eq_true.mp h F (List.mem_toFinset.mp hF))

-- The four faces in each half of the argument of Duval et al., Theorem 3.3.
private def probes : List Face :=
  let reflect : ℕ → ℕ
    | 0 => 7 | 7 => 0 | 2 => 4 | 4 => 2 | 6 => 8 | 8 => 6 | i => i
  (List.range 3).flatMap fun j => [false, true].flatMap fun mirror =>
    [[4, 8, 9], [1, 4, 8], [4, 5], [5, 7]].map fun s =>
      (s.map fun v => copyVertex j (if mirror then reflect v else v)).toFinset

private def candidates (s : Face) : List Face :=
  (facetsC.map List.toFinset).filter (s ⊆ ·)

-- Each recorded pair gives a facet and the intersection of the faces assigned to it.
private def commonFace (p : List (Face × Face)) (t s : Face) : Face :=
  match p.find? (fun x => x.1 == t) with
  | none => s
  | some x => x.2 ∩ s

-- Intervals [a,t] and [b,u] meet exactly when each bottom is contained in the other top:
-- their common face can then be taken to be a ∪ b.
private def compatible (p : List (Face × Face)) (t a : Face) : Bool :=
  p.all fun (u, b) => decide (t = u ∨ ¬ (a ⊆ u ∧ b ⊆ t))

private def search : List (Face × List Face) → List (Face × Face) → Bool
  | [], _ => true
  | (s, ts) :: todo, p =>
    ts.any fun t =>
      let a := commonFace p t s
      compatible p t a && search todo ((t, a) :: p)

private def Own (r : Face → Face) (t s : Face) : Prop :=
  IsFacet complexC t ∧ r t ⊆ s ∧ s ⊆ t

private theorem search_of_partition (r : Face → Face)
    (h : ∀ s ∈ complexC, ∃! t, Own r t s) (ss : List Face)
    (hss : ∀ s ∈ ss, s ∈ complexC) (p : List (Face × Face))
    (hp : ∀ x ∈ p, Own r x.1 x.2) :
    search (ss.map fun s => (s, candidates s)) p := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨t, ht, _⟩ := h s (hss s List.mem_cons_self)
    let a := commonFace p t s
    have ha : Own r t a := by
      unfold a commonFace
      split
      · exact ht
      · rename_i x hx
        have hm := hp x (List.mem_of_find?_eq_some hx)
        have he : x.1 = t := by simpa using List.find?_some hx
        rw [he] at hm
        exact ⟨ht.1, Finset.subset_inter hm.2.1 ht.2.1, Finset.inter_subset_right.trans ht.2.2⟩
    change (List.any (candidates s) _) = true
    apply List.any_eq_true.mpr
    obtain ⟨f, hf, hft⟩ := facet_list ht.1
    refine ⟨t, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨f, hf, hft⟩, by simpa using ht.2.2⟩, ?_⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨List.all_eq_true.mpr ?_, ih (fun u hu => hss u (List.mem_cons_of_mem _ hu)) _ ?_⟩
    · rintro ⟨u, b⟩ hx
      apply decide_eq_true
      by_contra! bad
      obtain ⟨hne, hat, hbt⟩ := bad
      have hb := hp (u, b) hx
      have hst : a ∪ b ⊆ t := Finset.union_subset ha.2.2 hbt
      have hs := h (a ∪ b) (complexC_simplicial _ ht.1.1 _ hst)
      exact hne (hs.unique ⟨ht.1, ha.2.1.trans Finset.subset_union_left, hst⟩
        ⟨hb.1, hb.2.1.trans Finset.subset_union_right, Finset.union_subset hat hb.2.2⟩)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hp x hx

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
-- Check every compatible assignment of the selected faces to covering tetrahedra.
private theorem complexC_nonpartitionable : ¬ IsPartitionable complexC := by
  rintro ⟨r, _, h⟩
  have hs : ∀ s ∈ probes, s ∈ complexC := by decide +kernel
  have hf : search (probes.map fun s => (s, candidates s)) [] = false := by decide +kernel
  exact Bool.noConfusion ((search_of_partition r h probes hs [] (by simp)).symm.trans hf)

/--
**The Stanley–Garsia partitionability conjecture is false.** There is a finite simplicial complex
on the vertex set $\mathbb{N}$ that is pure and Cohen–Macaulay over $\mathbb{Q}$ but not
partitionable.

Duval, Goeckner, Klivans and Martin constructed explicit pure $3$-dimensional Cohen–Macaulay
simplicial complexes that are not partitionable.

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic
Combinatorics (1999), Problem 6 (Stanley–Garsia partitionability conjecture); resolution: A. M.
Duval, B. Goeckner, C. J. Klivans and J. L. Martin, A non-partitionable Cohen-Macaulay simplicial
complex, Adv. Math. 299 (2016), 381-395, arXiv:1504.04279, Theorem 3.5 (arXiv numbering): the
complex C₃ obtained by gluing three copies of X along A is Cohen-Macaulay and non-partitionable
(Theorem 3.4: likewise C₂₅, by the gluing Theorem 3.1); abstract: "We disprove the conjecture by
constructing an explicit counterexample", https://arxiv.org/abs/1504.04279.
-/
theorem cohenMacaulayPartitionable_refuted : ¬ cohenMacaulayPartitionable := by
  intro h
  exact complexC_nonpartitionable (h complexC complexC_simplicial complexC_pure complexC_cm)

end MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted
