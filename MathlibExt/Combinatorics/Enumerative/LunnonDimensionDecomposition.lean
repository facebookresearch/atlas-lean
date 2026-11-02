/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

section
namespace MetaMathlibExt

open scoped BigOperators

/-- **Lattice cells.** For a natural number $d$, a lattice cell in dimension $d$ is a point of
$\mathbb{Z}^d$, that is, a function assigning an integer to each of the $d$ coordinate axes.

Source: Sebastian Luther and Stephan Mertens, *The Perimeter of Proper
Polycubes*, Journal of Integer Sequences 20 (2017), Article 17.9.5,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mertens/mert4.tex>:
a `d`-dimensional polycube is a set of face-connected cells in `ℤ^d`,
lines 115–117 (also arXiv:1705.03688v1). -/
def latticeCell (d : ℕ) : Type := Fin d → ℤ

/-- **Face adjacency of lattice cells.** Two lattice cells $x, y \in \mathbb{Z}^d$ are face
adjacent when there is an axis $k$ such that $x_j = y_j$ for every axis $j \ne k$ and
$|x_k - y_k| = 1$.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 277–279: this is the
"neighbors in the polycube" relation underlying the adjacency graph, in which two vertices
are connected if the corresponding cells are neighbors. -/
def faceAdjacent (d : ℕ) (x y : latticeCell d) : Prop :=
  ∃ k : Fin d, (∀ j : Fin d, j ≠ k → x j = y j) ∧ (y k = x k + 1 ∨ x k = y k + 1)

/-- **Polycube.** A finite set $S$ of lattice cells in $\mathbb{Z}^d$ is a polycube when it is
nonempty and any two cells $x, y \in S$ are joined by a finite sequence of cells of $S$, starting
at $x$ and ending at $y$, in which consecutive cells are face adjacent.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 115–117:
a `d`-dimensional polycube is a set of face-connected cells in `ℤ^d`.
Connectivity is expressed by reflexive transitive closure of face adjacency
restricted to the set `S`. -/
def isPolycubeCells (d : ℕ) (S : Finset (latticeCell d)) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S,
    Relation.ReflTransGen
      (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) x y

/-- **Canonical position of a cell set.** A finite set $S$ of lattice cells in $\mathbb{Z}^d$ is
in canonical position when, for every axis $k$, every cell $x \in S$ has $x_k \ge 0$ and some
cell $x \in S$ has $x_k = 0$; that is, the minimum of each coordinate over $S$ is $0$.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 115–117:
fixed polycubes are identified up to translation. Each class has a unique
representative with minima at zero. Only translations are quotiented, so
rotations and reflections stay distinct orientations. -/
def isCanonicalCells (d : ℕ) (S : Finset (latticeCell d)) : Prop :=
  ∀ k : Fin d, (∃ x ∈ S, x k = 0) ∧ ∀ x ∈ S, 0 ≤ x k

/-- **Proper dimension.** The proper dimension of a finite set $S$ of lattice cells in
$\mathbb{Z}^d$ is the number of axes $k$ on which $S$ varies, that is, for which there are
cells $x, y \in S$ with $x_k \ne y_k$.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 160–162:
a polycube spanning `i` dimensions is proper in `i` dimensions.
Asinowski–Barequet–Barequet–Rote, *Proper n-Cell Polycubes in n−3 Dimensions*,
Journal of Integer Sequences 15 (2012), Article 12.8.4, lines 171–172:
proper dimension is the dimension of the convex hull of cell centers, which for
axis-aligned cells equals the count of varying axes. -/
noncomputable def properDimension (d : ℕ) (S : Finset (latticeCell d)) : ℕ :=
  Nat.card { k : Fin d // ∃ x ∈ S, ∃ y ∈ S, x k ≠ y k }

/-- **Fixed polycubes.** For natural numbers $d$ and $n$, the fixed $n$-cell polycubes in
dimension $d$ are represented by the finite sets $S$ of lattice cells in $\mathbb{Z}^d$ that are
polycubes (nonempty and connected through face adjacency), have exactly $n$ cells, and are in
canonical position (the minimum of each coordinate over $S$ is $0$). -/
def fixedPolycube (d n : ℕ) : Type :=
  { S : Finset (latticeCell d) // isPolycubeCells d S ∧ S.card = n ∧ isCanonicalCells d S }

/-- **Number of fixed polycubes.** For natural numbers $d$ and $n$, $A_d(n)$ is the number of
fixed $n$-cell polycubes in dimension $d$, that is, the number of $n$-cell polycubes in
$\mathbb{Z}^d$ that are in canonical position. -/
noncomputable def fixedPolycubeCount (d n : ℕ) : ℕ :=
  Nat.card (fixedPolycube d n)

/-- **Proper fixed polycubes.** For natural numbers $n$ and $i$, the fixed $n$-cell polycubes
proper in dimension $i$ are the fixed $n$-cell polycubes in dimension $i$ whose proper dimension
is $i$, that is, which vary along each of the $i$ axes. -/
def properFixedPolycube (n i : ℕ) : Type :=
  { P : fixedPolycube i n // properDimension i P.val = i }

/-- **Number of proper fixed polycubes.** For natural numbers $n$ and $i$, $\mathrm{DX}(n,i)$ is
the number of fixed $n$-cell polycubes proper in dimension $i$, that is, of fixed $n$-cell
polycubes in dimension $i$ whose proper dimension is $i$.

Source: Asinowski et al., JIS 15 (2012), Article 12.8.4, line 978, state
$\mathrm{DX}(n,0) = 0$ for $n > 1$. -/
noncomputable def properFixedPolycubeCount (n i : ℕ) : ℕ :=
  Nat.card (properFixedPolycube n i)

-- ===== Helpers =====
private lemma faceAdjacent_symm_aux (d : ℕ) (x y : latticeCell d) :
    faceAdjacent d x y → faceAdjacent d y x :=
  fun ⟨k, hagree, hstep⟩ =>
    ⟨k, fun j hj => (hagree j hj).symm, by rcases hstep with h | h <;> [right; left] <;> omega⟩

private lemma faceAdjacent_irrefl_aux (d : ℕ) (x : latticeCell d) : ¬ faceAdjacent d x x := by
  rintro ⟨k, _, hstep⟩
  rcases hstep with h | h <;> omega

private lemma faceAdjacent_step_le_aux (d : ℕ) (x y : latticeCell d) (k : Fin d)
    (h : faceAdjacent d x y) : |x k - y k| ≤ 1 := by
  obtain ⟨k', hagree, hstep⟩ := h
  by_cases hk : k = k'
  · subst hk
    rcases hstep with h | h
    · rw [h]; simp
    · rw [h]; simp
  · rw [hagree k hk]; simp

private noncomputable def polyGraph_aux (d : ℕ) (S : Finset (latticeCell d)) : SimpleGraph ↥S :=
  SimpleGraph.mk
    (Adj := fun a b => faceAdjacent d (a : latticeCell d) (b : latticeCell d))
    (symm := Std.Symm.mk (fun _ _ h => by
      obtain ⟨k, hagree, hstep⟩ := h
      exact ⟨k, fun j hj => (hagree j
          hj).symm, by rcases hstep with h | h <;> [right; left] <;> omega⟩))
    (loopless := Std.Irrefl.mk (fun _ h => by
      obtain ⟨k, _, hstep⟩ := h
      rcases hstep with h | h <;> omega))

private lemma walk_coord_le_aux (d : ℕ) (S : Finset (latticeCell d)) (k : Fin d)
    {a b : ↥S} (w : (polyGraph_aux d S).Walk a b) :
    |(((b : latticeCell d) k) - ((a : latticeCell d) k))| ≤ (w.length : ℤ) := by
  induction w with
  | nil => simp
  | @cons u v w hadj tail ih =>
    have hadj' : faceAdjacent d (u : latticeCell d) (v : latticeCell d) := hadj
    have h0 := faceAdjacent_step_le_aux d (u : latticeCell d) (v : latticeCell d) k hadj'
    have hstep : |(((v : latticeCell d) k) - ((u : latticeCell d) k))| ≤ 1 := by
      rwa [abs_sub_comm]
    simp only [SimpleGraph.Walk.length_cons]
    push_cast
    have htri := abs_sub_le (((w : latticeCell d) k)) (((v : latticeCell d) k))
        (((u : latticeCell d) k))
    omega

private lemma walk_support_length_aux (d : ℕ) (S : Finset (latticeCell d))
    {a b : ↥S} (w : (polyGraph_aux d S).Walk a b) :
    w.support.length = w.length + 1 := by
  induction w with
  | nil => simp [SimpleGraph.Walk.support_nil]
  | cons hadj tail ih => simp [SimpleGraph.Walk.support_cons, ih, SimpleGraph.Walk.length_cons]

private lemma polyGraph_connected_aux (d : ℕ) (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S) : (polyGraph_aux d S).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨x0, hx0⟩ := hP.1
  refine ⟨⟨x0, hx0⟩, fun v => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  obtain ⟨y, hy⟩ := v
  have hRT := hP.2 x0 hx0 y hy
  have lift : ∀ (z : latticeCell d)
      (h : Relation.ReflTransGen
        (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) x0 z)
      (hz : z ∈ S),
        Relation.ReflTransGen (fun a b : ↥S => (polyGraph_aux d S).Adj a b)
          ⟨x0, hx0⟩ ⟨z, hz⟩ :=
    fun z h => Relation.ReflTransGen.rec
      (motive := fun z _ => ∀ hz : z ∈ S,
        Relation.ReflTransGen (fun a b : ↥S => (polyGraph_aux d S).Adj a b)
          ⟨x0, hx0⟩ ⟨z, hz⟩)
      (fun hz => by
        have he : (⟨x0, hx0⟩ : ↥S) = ⟨x0, hz⟩ := Subtype.ext rfl
        rw [he])
      (fun (hprev : Relation.ReflTransGen _ x0 _) (hstep : faceAdjacent d _ _ ∧ _ ∈ S ∧ _ ∈ S)
        (ih : ∀ hz, _) (hz : _ ∈ S) => by
        obtain ⟨hadj, hbS, _hcS⟩ := hstep
        have ih' := ih hbS
        have hsingle : (polyGraph_aux d S).Adj ⟨_, hbS⟩ (⟨_, hz⟩ : ↥S) := hadj
        exact ih'.tail hsingle)
      h
  exact lift y hRT hy

private lemma coord_lt_card_aux (d : ℕ) (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S) (hC : isCanonicalCells d S)
    (x : latticeCell d) (hx : x ∈ S) (k : Fin d) :
    x k < (S.card : ℤ) := by
  obtain ⟨x0, hx0, hx0k⟩ := (hC k).1
  have hRT := hP.2 x0 hx0 x hx
  have hreach : (polyGraph_aux d S).Reachable ⟨x0, hx0⟩ ⟨x, hx⟩ := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have lift : ∀ (z : latticeCell d)
        (h : Relation.ReflTransGen
          (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) x0 z)
        (hz : z ∈ S),
          Relation.ReflTransGen (fun a b : ↥S => (polyGraph_aux d S).Adj a b)
            ⟨x0, hx0⟩ ⟨z, hz⟩ :=
      fun z h => Relation.ReflTransGen.rec
        (motive := fun z _ => ∀ hz : z ∈ S,
          Relation.ReflTransGen (fun a b : ↥S => (polyGraph_aux d S).Adj a b)
            ⟨x0, hx0⟩ ⟨z, hz⟩)
        (fun hz => by
          have he : (⟨x0, hx0⟩ : ↥S) = ⟨x0, hz⟩ := Subtype.ext rfl
          rw [he])
        (fun (hprev : Relation.ReflTransGen _ x0 _) (hstep : faceAdjacent d _ _ ∧ _ ∈ S ∧ _ ∈ S)
          (ih : ∀ hz, _) (hz : _ ∈ S) => by
          obtain ⟨hadj, hbS, _hcS⟩ := hstep
          have ih' := ih hbS
          have hsingle : (polyGraph_aux d S).Adj ⟨_, hbS⟩ (⟨_, hz⟩ : ↥S) := hadj
          exact ih'.tail hsingle)
        h
    exact lift x hRT hx
  classical
  refine hreach.elim_path (fun p => by
    obtain ⟨w, hw⟩ := p
    rw [SimpleGraph.Walk.isPath_def] at hw
    have hlen_eq := walk_support_length_aux d S w
    have hnodup_le := List.Nodup.length_le_card (α := ↥S) hw
    rw [Fintype.card_coe] at hnodup_le
    have hbound := walk_coord_le_aux d S k w
    simp only at hbound
    rw [hx0k, sub_zero] at hbound
    have hlen_lt : w.length < S.card := by omega
    have hle : x k ≤ |x k| := le_abs_self _
    have hlt : (w.length : ℤ) < (S.card : ℤ) := by exact_mod_cast hlen_lt
    omega
  )

private def supportFinset_aux (d : ℕ) (S : Finset (latticeCell d)) : Finset (Fin d) :=
  Finset.univ.filter (fun k => ∃ x ∈ S, ∃ y ∈ S, x k ≠ y k)

private lemma properDimension_eq_support_aux (d : ℕ) (S : Finset (latticeCell d)) :
    properDimension d S = (supportFinset_aux d S).card := by
  unfold properDimension supportFinset_aux
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]

private noncomputable def encodeCell_aux (d n : ℕ) [NeZero n] (x : latticeCell d) :
    (Fin d → Fin n) :=
  fun k => ⟨(x k).toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩

private lemma encodeCell_eq_of_bounds_aux (d n : ℕ) [NeZero n] (x y : latticeCell d)
    (hxb : ∀ k : Fin d, 0 ≤ x k ∧ x k < (n : ℤ))
    (hyb : ∀ k : Fin d, 0 ≤ y k ∧ y k < (n : ℤ))
    (hxy : encodeCell_aux d n x = encodeCell_aux d n y) : x = y := by
  funext k
  have hxyk : (encodeCell_aux d n x) k = (encodeCell_aux d n y) k := by rw [hxy]
  simp only [encodeCell_aux] at hxyk
  have hmod : (x k).toNat % n = (y k).toNat % n := Fin.mk.injEq .. ▸ hxyk
  have h1 : (x k).toNat < n := by
    have h0 := (hxb k).1
    have h2 := (hxb k).2
    have h3 : ((x k).toNat : ℤ) = x k := Int.toNat_of_nonneg h0
    omega
  have h2 : (y k).toNat < n := by
    have h0 := (hyb k).1
    have h3 := (hyb k).2
    have h4 : ((y k).toNat : ℤ) = y k := Int.toNat_of_nonneg h0
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
  have hxnn := (hxb k).1
  have hynn := (hyb k).1
  have e1 : ((x k).toNat : ℤ) = x k := Int.toNat_of_nonneg hxnn
  have e2 : ((y k).toNat : ℤ) = y k := Int.toNat_of_nonneg hynn
  omega

private noncomputable def encodeSet_aux (d n : ℕ) [NeZero n] (P : fixedPolycube d n) :
    Finset (Fin d → Fin n) :=
  Finset.image (encodeCell_aux d n) P.val

private lemma encodeSet_injective_aux (d n : ℕ) [NeZero n] :
    Function.Injective (encodeSet_aux d n) := by
  intro P Q hPQ
  have hPS := P.2.1
  have hnS := P.2.2.1
  have hCS := P.2.2.2
  have hPT := Q.2.1
  have hnT := Q.2.2.1
  have hCT := Q.2.2.2
  set S := P.val with hSdef
  set T := Q.val with hTdef
  have bS : ∀ x ∈ S, ∀ k : Fin d, 0 ≤ x k ∧ x k < (n : ℤ) := by
    intro x hx k
    refine ⟨(hCS k).2 x hx, ?_⟩
    have hb := coord_lt_card_aux d S hPS hCS x hx k
    rw [hnS] at hb
    exact hb
  have bT : ∀ y ∈ T, ∀ k : Fin d, 0 ≤ y k ∧ y k < (n : ℤ) := by
    intro y hy k
    refine ⟨(hCT k).2 y hy, ?_⟩
    have hb := coord_lt_card_aux d T hPT hCT y hy k
    rw [hnT] at hb
    exact hb
  have himg : Finset.image (encodeCell_aux d n) S =
      Finset.image (encodeCell_aux d n) T := hPQ
  have hST : S ⊆ T := by
    intro x hx
    have hmem : encodeCell_aux d n x ∈ Finset.image (encodeCell_aux d n) T := by
      rw [← himg]
      exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hmem
    have heq : x = y :=
      encodeCell_eq_of_bounds_aux d n x y (bS x hx) (bT y hy) hyx.symm
    rw [heq]
    exact hy
  have hTS : T ⊆ S := by
    intro y hy
    have hmem : encodeCell_aux d n y ∈ Finset.image (encodeCell_aux d n) S := by
      rw [himg]
      exact Finset.mem_image_of_mem _ hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
    have heq : y = x :=
      encodeCell_eq_of_bounds_aux d n y x (bT y hy) (bS x hx) hxy.symm
    rw [heq]
    exact hx
  have hSTeq : S = T := Finset.Subset.antisymm hST hTS
  exact Subtype.ext hSTeq

private instance finite_fixedNeZero_aux (d n : ℕ) [NeZero n] : Finite (fixedPolycube d n) :=
  Finite.of_injective (encodeSet_aux d n) (encodeSet_injective_aux d n)

private instance fixedEmpty_aux (d : ℕ) : IsEmpty (fixedPolycube d 0) := by
  constructor
  intro P
  obtain ⟨S, ⟨hP, hn, _⟩⟩ := P
  obtain ⟨x0, _⟩ := hP.1
  have : S.card > 0 := Finset.card_pos.mpr ⟨x0, ‹x0 ∈ S›⟩
  omega

private instance finite_fixed_aux (d n : ℕ) : Finite (fixedPolycube d n) := by
  by_cases hn : n = 0
  · subst hn
    have := fixedEmpty_aux d
    have := Fintype.ofIsEmpty (α := fixedPolycube d 0)
    exact Finite.of_fintype _
  · have : NeZero n := ⟨hn⟩
    exact finite_fixedNeZero_aux d n

private instance finite_proper_aux (n i : ℕ) : Finite (properFixedPolycube n i) :=
  Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)

-- axis uniqueness: differing axis must be the face-adjacency axis
private lemma faceAdjacent_axis_unique_aux (d : ℕ) (x y : latticeCell d) (k k' : Fin d)
    (_h : faceAdjacent d x y)
    (hagree : ∀ j : Fin d, j ≠ k' → x j = y j)
    (hdiff : x k ≠ y k) : k = k' := by
  by_contra hne
  exact hdiff (hagree k hne)

private lemma faceAdjacent_axis_unique_aux2 (d : ℕ) (x y : latticeCell d) (k k' : Fin d)
    (hagree : ∀ j : Fin d, j ≠ k' → x j = y j)
    (hdiff : x k ≠ y k) : k = k' := by
  by_contra hne
  exact hdiff (hagree k hne)

private lemma walk_exists_edge_diff_generic_aux (d : ℕ) (S : Finset (latticeCell d))
    (G : SimpleGraph ↥S) (k : Fin d)
    {a b : ↥S} (w : G.Walk a b)
    (hdiff : ((a : latticeCell d) k) ≠ ((b : latticeCell d) k)) :
    ∃ e ∈ w.edges, ∃ u v : ↥S, e = s(u, v) ∧ G.Adj u v ∧
      ((u : latticeCell d) k) ≠ ((v : latticeCell d) k) := by
  induction w with
  | nil => simp at hdiff
  | @cons u v w hadj tail ih =>
    by_cases heq : ((u : latticeCell d) k) = ((v : latticeCell d) k)
    · have hdiff' : ((v : latticeCell d) k) ≠ ((w : latticeCell d) k) := by omega
      obtain ⟨e, he, u', v', heq2, hadj', hne⟩ := ih hdiff'
      refine ⟨e, ?_, u', v', heq2, hadj', hne⟩
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_of_mem _ he
    · refine ⟨s(u, v), ?_, u, v, rfl, hadj, heq⟩
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_self

private noncomputable def compressCell_aux2 (d : ℕ) (A : Finset (Fin d))
    (x : latticeCell d) : latticeCell A.card :=
  fun i => x ((Finset.orderIsoOfFin A rfl i : ↥A).val)

private noncomputable def expandCell_aux2 (d : ℕ) (A : Finset (Fin d))
    (y : latticeCell A.card) : latticeCell d :=
  fun k => if h : k ∈ A then y ((Finset.orderIsoOfFin A rfl).symm ⟨k, h⟩) else 0

private lemma compress_expand_aux2 (d : ℕ) (A : Finset (Fin d))
    (y : latticeCell A.card) :
    compressCell_aux2 d A (expandCell_aux2 d A y) = y := by
  funext i
  simp only [compressCell_aux2, expandCell_aux2]
  have hmem : ((Finset.orderIsoOfFin A rfl i : ↥A).val) ∈ A :=
    (Finset.orderIsoOfFin A rfl i).property
  rw [dite_eq_left hmem]
  have heq : (⟨((Finset.orderIsoOfFin A rfl i : ↥A).val), hmem⟩ : ↥A) =
      Finset.orderIsoOfFin A rfl i := Subtype.ext rfl
  rw [heq, OrderIso.symm_apply_apply]

private lemma expand_compress_aux2 (d : ℕ) (A : Finset (Fin d))
    (x : latticeCell d) (hz : ∀ k : Fin d, k ∉ A → x k = 0) :
    expandCell_aux2 d A (compressCell_aux2 d A x) = x := by
  funext k
  simp only [expandCell_aux2, compressCell_aux2]
  by_cases hk : k ∈ A
  · rw [dite_eq_left hk]
    obtain ⟨i, hi⟩ := (Finset.orderIsoOfFin A rfl).surjective ⟨k, hk⟩
    have hsym : (Finset.orderIsoOfFin A rfl).symm ⟨k, hk⟩ = i := by
      rw [← hi]
      exact OrderIso.symm_apply_apply (Finset.orderIsoOfFin A rfl) i
    rw [hsym, hi]
  · rw [dite_eq_right hk, hz k hk]

private lemma support_card_lt_aux (d n : ℕ) (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S) (hn : S.card = n) :
    (supportFinset_aux d S).card < n := by
  classical
  have hconn := polyGraph_connected_aux d S hP
  obtain ⟨T, hle, hTree⟩ := SimpleGraph.Connected.exists_isTree_le hconn
  have : DecidableEq ↥S := Classical.typeDecidableEq _
  have : DecidableRel T.Adj := Classical.decRel _
  have := SimpleGraph.fintypeEdgeSet T
  have hcard := hTree.card_edgeFinset
  rw [Fintype.card_coe, hn] at hcard
  let axisSet : Sym2 ↥S → Finset (Fin d) := fun e =>
    Finset.univ.filter (fun k => ∃ u v : ↥S, e = s(u, v) ∧ T.Adj u v ∧
      ((u : latticeCell d) k) ≠ ((v : latticeCell d) k))
  have haxis1 : ∀ e ∈ T.edgeFinset, (axisSet e).card ≤ 1 := by
    intro e he
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [axisSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨u1, v1, he1, hadj1, hne1⟩ := ha
    obtain ⟨u2, v2, he2, hadj2, hne2⟩ := hb
    have hf1 : faceAdjacent d (u1 : latticeCell d) (v1 : latticeCell d) := hle hadj1
    obtain ⟨k1, hagree1, _⟩ := hf1
    have ha1 : a = k1 := faceAdjacent_axis_unique_aux2 d _ _ a k1 hagree1 hne1
    have heq : s(u1, v1) = s(u2, v2) := by rw [← he1, ← he2]
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · have hne1' : ((u1 : latticeCell d) b) ≠ ((v1 : latticeCell d) b) := hne2
      have hb1 : b = k1 := faceAdjacent_axis_unique_aux2 d _ _ b k1 hagree1 hne1'
      omega
    · subst h1
      subst h2
      simp only [ne_eq]at hne2
      have hne1' : ((u1 : latticeCell d) b) ≠ ((v1 : latticeCell d) b) := Ne.symm hne2
      have hb1 : b = k1 := faceAdjacent_axis_unique_aux2 d _ _ b k1 hagree1 hne1'
      omega
  have hsub : supportFinset_aux d S ⊆ T.edgeFinset.biUnion axisSet := by
    intro k hk
    simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨x, hx, y, hy, hxy⟩ := hk
    have hTconn := hTree.connected
    rw [SimpleGraph.connected_iff_exists_forall_reachable] at hTconn
    obtain ⟨r, hr⟩ := hTconn
    have hreach : T.Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
      (hr ⟨x, hx⟩).symm.trans (hr ⟨y, hy⟩)
    have hex : ∃ w : T.Walk ⟨x, hx⟩ ⟨y, hy⟩,
        ∃ e ∈ w.edges, ∃ u v : ↥S, e = s(u, v) ∧ T.Adj u v ∧
          ((u : latticeCell d) k) ≠ ((v : latticeCell d) k) := by
      refine hreach.elim_path (fun p => ?_)
      obtain ⟨w, _hw⟩ := p
      have hdiff : (((⟨x, hx⟩ : ↥S) : latticeCell d) k) ≠
          (((⟨y, hy⟩ : ↥S) : latticeCell d) k) := hxy
      refine ⟨w, walk_exists_edge_diff_generic_aux d S T k w hdiff⟩
    obtain ⟨w, e, he, u, v, heq, hadj, hne⟩ := hex
    have hedge : e ∈ T.edgeSet := w.edges_subset_edgeSet he
    have hefin : e ∈ T.edgeFinset := (SimpleGraph.mem_edgeFinset).mpr hedge
    exact Finset.mem_biUnion.mpr ⟨e, hefin, by
      simp only [axisSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, v, heq, hadj, hne⟩⟩
  have h1 : (supportFinset_aux d S).card ≤ (T.edgeFinset.biUnion axisSet).card :=
    Finset.card_le_card hsub
  have h2 : (T.edgeFinset.biUnion axisSet).card ≤
      ∑ e ∈ T.edgeFinset, (axisSet e).card := Finset.card_biUnion_le
  have hsum : ∑ e ∈ T.edgeFinset, (axisSet e).card ≤ T.edgeFinset.card := by
    calc ∑ e ∈ T.edgeFinset, (axisSet e).card
        ≤ ∑ _e ∈ T.edgeFinset, 1 := Finset.sum_le_sum haxis1
      _ = T.edgeFinset.card := by simp
  omega

private lemma compress_preserves_adj_aux2 (d : ℕ) (A : Finset (Fin d))
    (x y : latticeCell d)
    (hxz : ∀ k : Fin d, k ∉ A → x k = 0)
    (hyz : ∀ k : Fin d, k ∉ A → y k = 0)
    (h : faceAdjacent d x y) :
    faceAdjacent A.card (compressCell_aux2 d A x) (compressCell_aux2 d A y) := by
  obtain ⟨k', hagree, hstep⟩ := h
  have hdiff : x k' ≠ y k' := by
    rcases hstep with h | h <;> omega
  have hk'A : k' ∈ A := by
    by_contra hnotin
    rw [hxz k' hnotin, hyz k' hnotin] at hdiff
    exact hdiff rfl
  let e := Finset.orderIsoOfFin A rfl
  obtain ⟨i', hi'⟩ := e.surjective ⟨k', hk'A⟩
  refine ⟨i', ?_, ?_⟩
  · intro j hj
    change x ((e j : ↥A).val) = y ((e j : ↥A).val)
    apply hagree
    intro heq
    apply hj
    have hval : ((e i' : ↥A).val) = k' := congrArg Subtype.val hi'
    have heq' : e j = e i' := by
      apply Subtype.ext
      show ((e j : ↥A).val) = ((e i' : ↥A).val)
      rw [heq, hval]
    exact e.injective heq'
  · change (y ((e i' : ↥A).val) = x ((e i' : ↥A).val) + 1 ∨
      x ((e i' : ↥A).val) = y ((e i' : ↥A).val) + 1)
    have hval : ((e i' : ↥A).val) = k' := congrArg Subtype.val hi'
    rw [hval]
    exact hstep

private lemma expand_preserves_adj_aux2 (d : ℕ) (A : Finset (Fin d))
    (y1 y2 : latticeCell A.card)
    (h : faceAdjacent A.card y1 y2) :
    faceAdjacent d (expandCell_aux2 d A y1) (expandCell_aux2 d A y2) := by
  obtain ⟨i', hagree, hstep⟩ := h
  let e := Finset.orderIsoOfFin A rfl
  have hk' : ((e i' : ↥A).val) ∈ A := (e i').property
  refine ⟨(e i' : ↥A).val, ?_, ?_⟩
  · intro j hj
    show expandCell_aux2 d A y1 j = expandCell_aux2 d A y2 j
    simp only [expandCell_aux2]
    by_cases hjA : j ∈ A
    · rw [dite_eq_left hjA, dite_eq_left hjA]
      have hne : e.symm ⟨j, hjA⟩ ≠ i' := by
        intro heq
        apply hj
        have h1 : e (e.symm ⟨j, hjA⟩) = (⟨j, hjA⟩ : ↥A) :=
          OrderIso.apply_symm_apply e _
        rw [heq] at h1
        have h2 : ((e i' : ↥A).val) = j := congrArg Subtype.val h1
        exact h2.symm
      exact hagree _ hne
    · rw [dite_eq_right hjA, dite_eq_right hjA]
  · have hY1 : expandCell_aux2 d A y1 ((e i' : ↥A).val) = y1 i' := by
      simp only [expandCell_aux2]
      rw [dite_eq_left hk']
      have heq : (⟨((e i' : ↥A).val), hk'⟩ : ↥A) = e i' := Subtype.ext rfl
      rw [heq, OrderIso.symm_apply_apply]
    have hY2 : expandCell_aux2 d A y2 ((e i' : ↥A).val) = y2 i' := by
      simp only [expandCell_aux2]
      rw [dite_eq_left hk']
      have heq : (⟨((e i' : ↥A).val), hk'⟩ : ↥A) = e i' := Subtype.ext rfl
      rw [heq, OrderIso.symm_apply_apply]
    rw [hY2, hY1]
    exact hstep

private lemma zero_outside_of_not_mem_support_aux (d : ℕ) (S : Finset (latticeCell d))
    (hC : isCanonicalCells d S) (k : Fin d) (hk : k ∉ supportFinset_aux d S)
    (x : latticeCell d) (hx : x ∈ S) : x k = 0 := by
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and,
    not_exists] at hk
  have hall : ∀ y ∈ S, x k = y k := by
    intro y hy
    by_contra hne
    exact hk x ⟨hx, y, hy, hne⟩
  obtain ⟨x0, hx0, hx0k⟩ := (hC k).1
  have h := hall x0 hx0
  rw [hx0k] at h
  exact h

private lemma properDimension_lt_aux (d n : ℕ) (P : fixedPolycube d n) :
    properDimension d P.val < n := by
  rw [properDimension_eq_support_aux]
  exact support_card_lt_aux d n P.val P.2.1 P.2.2.1

private lemma vanish_DX_ge_aux (n i : ℕ) (h : n ≤ i) : properFixedPolycubeCount n i = 0 := by
  unfold properFixedPolycubeCount
  rw [Nat.card_eq_zero]
  left
  constructor
  intro Q
  obtain ⟨P, hP⟩ := Q
  -- P : fixedPolycube i n with properDimension = i, but < n ≤ i contradiction
  have hlt := properDimension_lt_aux i n P
  omega

private instance subsingleton_cell_zero_aux : Subsingleton (latticeCell 0) := by
  constructor
  intro x y
  funext k
  exact Fin.elim0 k

private lemma vanish_DX_zero_aux (n : ℕ) (hn : 1 < n) : properFixedPolycubeCount n 0 = 0 := by
  unfold properFixedPolycubeCount
  rw [Nat.card_eq_zero]
  left
  constructor
  intro Q
  obtain ⟨P, _hP⟩ := Q
  obtain ⟨S, ⟨_hS, hnS, _hC⟩⟩ := P
  -- S : Finset (latticeCell 0) with card = n > 1, but Subsingleton gives ≤1
  have hle : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a _ b _
    exact Subsingleton.elim a b
  omega

private instance latticeCellDecEq_aux (d : ℕ) : DecidableEq (latticeCell d) :=
  inferInstanceAs (DecidableEq (Fin d → ℤ))

-- fiber over support A
private def fiberSet_aux (d n : ℕ) (A : Finset (Fin d)) : Type :=
  { P : fixedPolycube d n // supportFinset_aux d P.val = A }

private instance finite_fiber_aux (d n : ℕ) (A : Finset (Fin d)) :
    Finite (fiberSet_aux d n A) :=
  Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)

-- compress/expand on Finsets (images)
private noncomputable def compressSet_aux2 (d : ℕ) (A : Finset (Fin d))
    (S : Finset (latticeCell d)) : Finset (latticeCell A.card) :=
  Finset.image (compressCell_aux2 d A) S

private noncomputable def expandSet_aux2 (d : ℕ) (A : Finset (Fin d))
    (T : Finset (latticeCell A.card)) : Finset (latticeCell d) :=
  Finset.image (expandCell_aux2 d A) T

-- compress is injective on cells vanishing outside A
private lemma compress_injOn_zero_outside_aux (d : ℕ) (A : Finset (Fin d)) :
    Set.InjOn (compressCell_aux2 d A) { x | ∀ k : Fin d, k ∉ A → x k = 0 } := by
  intro x hx y hy hxy
  simp only [Set.mem_ofPred_eq] at hx hy
  have hx' : expandCell_aux2 d A (compressCell_aux2 d A x) = x :=
    expand_compress_aux2 d A x hx
  have hy' : expandCell_aux2 d A (compressCell_aux2 d A y) = y :=
    expand_compress_aux2 d A y hy
  rw [← hx', ← hy', hxy]

-- expand is always injective
private lemma expand_injective_aux (d : ℕ) (A : Finset (Fin d)) :
    Function.Injective (expandCell_aux2 d A) := by
  intro y1 y2 h
  have h2 := congrArg (compressCell_aux2 d A) h
  rwa [compress_expand_aux2, compress_expand_aux2] at h2

private lemma card_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    (compressSet_aux2 d A S).card = S.card := by
  unfold compressSet_aux2
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  simp only [Finset.mem_coe] at hx hy
  exact compress_injOn_zero_outside_aux d A (hz x hx) (hz y hy) hxy

private lemma card_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card)) :
    (expandSet_aux2 d A T).card = T.card := by
  unfold expandSet_aux2
  exact Finset.card_image_of_injective T (expand_injective_aux d A)

private lemma canon_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hC : isCanonicalCells d S) :
    isCanonicalCells A.card (compressSet_aux2 d A S) := by
  intro j
  obtain ⟨x0, hx0, hx0k⟩ :=
    (hC ((Finset.orderIsoOfFin A rfl j : ↥A).val)).1
  constructor
  · refine ⟨compressCell_aux2 d A x0, Finset.mem_image_of_mem _ hx0, ?_⟩
    change x0 ((Finset.orderIsoOfFin A rfl j : ↥A).val) = 0
    exact hx0k
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ y ((Finset.orderIsoOfFin A rfl j : ↥A).val)
    exact (hC ((Finset.orderIsoOfFin A rfl j : ↥A).val)).2 y hy

private lemma canon_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card))
    (hTne : T.Nonempty) (hC : isCanonicalCells A.card T) :
    isCanonicalCells d (expandSet_aux2 d A T) := by
  intro k
  by_cases hk : k ∈ A
  · obtain ⟨y0, hy0, hy0j⟩ :=
      (hC ((Finset.orderIsoOfFin A rfl).symm ⟨k, hk⟩)).1
    constructor
    · refine ⟨expandCell_aux2 d A y0, Finset.mem_image_of_mem _ hy0, ?_⟩
      simp only [expandCell_aux2, dite_eq_left hk]
      exact hy0j
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simp only [expandCell_aux2, dite_eq_left hk]
      exact (hC ((Finset.orderIsoOfFin A rfl).symm ⟨k, hk⟩)).2 y hy
  · constructor
    · obtain ⟨y0, hy0⟩ := hTne
      refine ⟨expandCell_aux2 d A y0, Finset.mem_image_of_mem _ hy0, ?_⟩
      simp only [expandCell_aux2, dite_eq_right hk]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simp only [expandCell_aux2, dite_eq_right hk, le_refl]

private lemma conn_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S)
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    isPolycubeCells A.card (compressSet_aux2 d A S) := by
  constructor
  · obtain ⟨x0, hx0⟩ := hP.1
    exact ⟨compressCell_aux2 d A x0, Finset.mem_image_of_mem _ hx0⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hRT := hP.2 x hx y hy
    have hmono : (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) ≤
        Function.onFun (fun a' b' : latticeCell A.card =>
          faceAdjacent A.card a' b' ∧
            a' ∈ compressSet_aux2 d A S ∧ b' ∈ compressSet_aux2 d A S)
        (compressCell_aux2 d A) := by
      intro u v huv
      obtain ⟨hadj, huS, hvS⟩ := huv
      refine ⟨compress_preserves_adj_aux2 d A u v (hz u huS) (hz v hvS) hadj, ?_, ?_⟩
      · exact Finset.mem_image_of_mem _ huS
      · exact Finset.mem_image_of_mem _ hvS
    exact Relation.ReflTransGen.lift (compressCell_aux2 d A) hmono _ _ hRT

private lemma conn_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card))
    (hPT : isPolycubeCells A.card T) :
    isPolycubeCells d (expandSet_aux2 d A T) := by
  constructor
  · obtain ⟨y0, hy0⟩ := hPT.1
    exact ⟨expandCell_aux2 d A y0, Finset.mem_image_of_mem _ hy0⟩
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have hRT := hPT.2 u hu v hv
    have hmono : (fun a b : latticeCell A.card =>
          faceAdjacent A.card a b ∧ a ∈ T ∧ b ∈ T) ≤
        Function.onFun (fun a' b' : latticeCell d =>
          faceAdjacent d a' b' ∧
            a' ∈ expandSet_aux2 d A T ∧ b' ∈ expandSet_aux2 d A T)
        (expandCell_aux2 d A) := by
      intro u' v' huv
      obtain ⟨hadj, huT, hvT⟩ := huv
      refine ⟨expand_preserves_adj_aux2 d A u' v' hadj, ?_, ?_⟩
      · exact Finset.mem_image_of_mem _ huT
      · exact Finset.mem_image_of_mem _ hvT
    exact Relation.ReflTransGen.lift (expandCell_aux2 d A) hmono _ _ hRT

private lemma support_compressSet_aux (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hsup : supportFinset_aux d S = A) :
    supportFinset_aux A.card (compressSet_aux2 d A S) = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro j
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and]
  have hkA : (Finset.orderIsoOfFin A rfl j : ↥A).val ∈ A :=
    (Finset.orderIsoOfFin A rfl j).property
  have hkS : (Finset.orderIsoOfFin A rfl j : ↥A).val ∈ supportFinset_aux d S := by
    rw [hsup]
    exact hkA
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
  obtain ⟨x, hx, y, hy, hxy⟩ := hkS
  refine ⟨compressCell_aux2 d A x, Finset.mem_image_of_mem _ hx,
    compressCell_aux2 d A y, Finset.mem_image_of_mem _ hy, ?_⟩
  change x ((Finset.orderIsoOfFin A rfl j : ↥A).val) ≠
    y ((Finset.orderIsoOfFin A rfl j : ↥A).val)
  exact hxy

private lemma support_expandSet_aux (d : ℕ) (A : Finset (Fin d)) (T : Finset (latticeCell A.card))
    (hsup : supportFinset_aux A.card T = Finset.univ) :
    supportFinset_aux d (expandSet_aux2 d A T) = A := by
  ext k
  simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, v, hv, hne⟩
    by_contra hkA
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y2, hy2, rfl⟩ := Finset.mem_image.mp hv
    have e1 : expandCell_aux2 d A y1 k = 0 := by
      simp only [expandCell_aux2, dite_eq_right hkA]
    have e2 : expandCell_aux2 d A y2 k = 0 := by
      simp only [expandCell_aux2, dite_eq_right hkA]
    rw [e1, e2] at hne
    exact hne rfl
  · intro hkA
    have hjU : (Finset.orderIsoOfFin A rfl).symm ⟨k, hkA⟩ ∈
        (Finset.univ : Finset (Fin A.card)) := Finset.mem_univ _
    rw [← hsup] at hjU
    simp only [supportFinset_aux, Finset.mem_filter, Finset.mem_univ, true_and] at hjU
    obtain ⟨y1, hy1, y2, hy2, hne⟩ := hjU
    refine ⟨expandCell_aux2 d A y1, Finset.mem_image_of_mem _ hy1,
      expandCell_aux2 d A y2, Finset.mem_image_of_mem _ hy2, ?_⟩
    show expandCell_aux2 d A y1 k ≠ expandCell_aux2 d A y2 k
    simp only [expandCell_aux2, dite_eq_left hkA]
    exact hne

private lemma expand_compressSet_aux2 (d : ℕ) (A : Finset (Fin d)) (S : Finset (latticeCell d))
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    expandSet_aux2 d A (compressSet_aux2 d A S) = S := by
  unfold expandSet_aux2 compressSet_aux2
  rw [Finset.image_image]
  have h : Set.EqOn (expandCell_aux2 d A ∘ compressCell_aux2 d A) id ↑S := by
    intro x hx
    simp only [Finset.mem_coe] at hx
    change expandCell_aux2 d A (compressCell_aux2 d A x) = id x
    rw [expand_compress_aux2 d A x (hz x hx)]
    rfl
  rw [Finset.image_congr h, Finset.image_id]

private lemma compress_expandSet_aux2 (d : ℕ) (A : Finset (Fin d))
    (T : Finset (latticeCell A.card)) :
    compressSet_aux2 d A (expandSet_aux2 d A T) = T := by
  unfold compressSet_aux2 expandSet_aux2
  rw [Finset.image_image]
  have h : Set.EqOn (compressCell_aux2 d A ∘ expandCell_aux2 d A) id ↑T := by
    intro y _
    change compressCell_aux2 d A (expandCell_aux2 d A y) = id y
    rw [compress_expand_aux2 d A y]
    rfl
  rw [Finset.image_congr h, Finset.image_id]

private noncomputable def fiberToProper_aux (d n : ℕ) (A : Finset (Fin d))
    (P : fiberSet_aux d n A) : properFixedPolycube n A.card :=
  match P with
  | ⟨⟨S, hP, hnS, hC⟩, hsup⟩ =>
    have hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0 := by
      intro x hx k hkA
      have hkn : k ∉ supportFinset_aux d S := by
        rw [hsup]
        exact hkA
      exact zero_outside_of_not_mem_support_aux d S hC k hkn x hx
    ⟨⟨compressSet_aux2 d A S,
      conn_compressSet_aux d A S hP hz,
      by rw [card_compressSet_aux d A S hz, hnS],
      canon_compressSet_aux d A S hC⟩,
    by rw [properDimension_eq_support_aux, support_compressSet_aux d A S hsup,
      Finset.card_univ, Fintype.card_fin]⟩

private noncomputable def properToFiber_aux (d n : ℕ) (A : Finset (Fin d))
    (Q : properFixedPolycube n A.card) : fiberSet_aux d n A :=
  match Q with
  | ⟨⟨T, hPT, hnT, hCT⟩, hproper⟩ =>
    have hsupT : supportFinset_aux A.card T = Finset.univ := by
      have h1 : (supportFinset_aux A.card T).card = Fintype.card (Fin A.card) := by
        rw [← properDimension_eq_support_aux, hproper, Fintype.card_fin]
      exact Finset.eq_univ_of_card _ h1
    ⟨⟨expandSet_aux2 d A T,
      conn_expandSet_aux d A T hPT,
      by rw [card_expandSet_aux d A T, hnT],
      canon_expandSet_aux d A T hPT.1 hCT⟩,
    support_expandSet_aux d A T hsupT⟩

private lemma fiberToProper_explicit_aux (d n : ℕ) (A : Finset (Fin d))
    (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S) (hnS : S.card = n) (hC : isCanonicalCells d S)
    (hsup : supportFinset_aux d S = A)
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    fiberToProper_aux d n A ⟨⟨S, hP, hnS, hC⟩, hsup⟩ =
      (⟨⟨compressSet_aux2 d A S,
        conn_compressSet_aux d A S hP hz,
        by rw [card_compressSet_aux d A S hz, hnS],
        canon_compressSet_aux d A S hC⟩,
      by rw [properDimension_eq_support_aux, support_compressSet_aux d A S hsup,
        Finset.card_univ, Fintype.card_fin]⟩ :
      properFixedPolycube n A.card) := rfl

private lemma properToFiber_explicit_aux (d n : ℕ) (A : Finset (Fin d))
    (T : Finset (latticeCell A.card))
    (hPT : isPolycubeCells A.card T) (hnT : T.card = n)
    (hCT : isCanonicalCells A.card T)
    (hproper : properDimension A.card T = A.card) :
    properToFiber_aux d n A ⟨⟨T, hPT, hnT, hCT⟩, hproper⟩ =
      (⟨⟨expandSet_aux2 d A T,
        conn_expandSet_aux d A T hPT,
        by rw [card_expandSet_aux d A T, hnT],
        canon_expandSet_aux d A T hPT.1 hCT⟩,
      support_expandSet_aux d A T (by
        have h1 : (supportFinset_aux A.card T).card = Fintype.card (Fin A.card) := by
          rw [← properDimension_eq_support_aux, hproper, Fintype.card_fin]
        exact Finset.eq_univ_of_card _ h1)⟩ :
      fiberSet_aux d n A) := rfl

private noncomputable def fiberEquivProper_aux (d n : ℕ) (A : Finset (Fin d)) :
    fiberSet_aux d n A ≃ properFixedPolycube n A.card where
  toFun := fiberToProper_aux d n A
  invFun := properToFiber_aux d n A
  left_inv := by
    rintro ⟨⟨S, hP, hnS, hC⟩, hsup⟩
    have hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0 := by
      intro x hx k hkA
      have hkn : k ∉ supportFinset_aux d S := by
        rw [hsup]
        exact hkA
      exact zero_outside_of_not_mem_support_aux d S hC k hkn x hx
    rw [fiberToProper_explicit_aux d n A S hP hnS hC hsup hz]
    apply Subtype.ext
    apply Subtype.ext
    change expandSet_aux2 d A (compressSet_aux2 d A S) = S
    exact expand_compressSet_aux2 d A S hz
  right_inv := by
    rintro ⟨⟨T, hPT, hnT, hCT⟩, hproper⟩
    rw [properToFiber_explicit_aux d n A T hPT hnT hCT hproper]
    apply Subtype.ext
    apply Subtype.ext
    change compressSet_aux2 d A (expandSet_aux2 d A T) = T
    exact compress_expandSet_aux2 d A T

private lemma fiber_card_eq_DX_aux (d n : ℕ) (A : Finset (Fin d)) :
    Nat.card (fiberSet_aux d n A) = properFixedPolycubeCount n A.card := by
  unfold properFixedPolycubeCount
  exact Nat.card_congr (fiberEquivProper_aux d n A)

private noncomputable def sigmaFiberEquiv_aux (d n : ℕ) :
    (Σ A : Finset (Fin d), fiberSet_aux d n A) ≃ fixedPolycube d n where
  toFun := fun ⟨A, P, _⟩ => P
  invFun := fun P => ⟨supportFinset_aux d P.val, P, rfl⟩
  left_inv := by
    rintro ⟨A, P, h⟩
    subst h
    rfl
  right_inv := by
    intro P
    rfl

private lemma card_eq_sum_fiber_aux (d n : ℕ) :
    Nat.card (fixedPolycube d n) =
      ∑ A : Finset (Fin d), Nat.card (fiberSet_aux d n A) := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (sigmaFiberEquiv_aux d n).symm

private lemma sum_fiber_eq_range_aux (d n : ℕ) :
    (∑ A : Finset (Fin d), Nat.card (fiberSet_aux d n A)) =
      ∑ m ∈ Finset.range (d + 1), d.choose m * properFixedPolycubeCount n m := by
  simp_rw [fiber_card_eq_DX_aux d n]
  have h2 := Finset.sum_powerset_apply_card (α := ℕ)
    (fun m => properFixedPolycubeCount n m) (x := (Finset.univ : Finset (Fin d)))
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [← Finset.powerset_univ]
  rw [h2]
  apply Finset.sum_congr rfl
  intro m _
  rw [nsmul_eq_mul, Nat.cast_id]

/-- **Lunnon's dimension decomposition for fixed polycubes.** Let $d$ and $n$ be natural numbers
with $n > 1$, let $A_d(n)$ be the number of fixed $n$-cell polycubes in dimension $d$, and for
each $i$ let $\mathrm{DX}(n,i)$ be the number of fixed $n$-cell polycubes proper in dimension $i$.
Then

$$A_d(n) = \sum_{i=1}^{n-1} \binom{d}{i} \, \mathrm{DX}(n,i).$$

The hypothesis $n > 1$ is needed: the printed formula omits its domain and fails at $n = 1$,
where the single cell is a polycube proper in dimension $0$ and so is counted only by the
$i = 0$ term, which the sum excludes. For $n > 1$ that term vanishes, since
$\mathrm{DX}(n,0) = 0$.

Proves `Wanted` entry `lunnon_fixed_polycube_dimension_decomposition`.

Sources: Sebastian Luther and Stephan Mertens, *The Perimeter of Proper
Polycubes*, Journal of Integer Sequences 20 (2017), Article 17.9.5,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mertens/mert4.tex>:
Lunnon's classical formula `eq:lunnon-a`, lines 172–175, with sum
`i = 1, …, n-1` and factor `C(d,i)`; `DX` notation and the at-most-`n-1`
dimensions bound, lines 163–166. Original: W. F. Lunnon, *Counting
multidimensional polyominoes*, Comput. J. 18 (1975), 366–367.
`DX(n,0) = 0` for `n > 1` from Asinowski–Barequet–Barequet–Rote, JIS 15
(2012), Article 12.8.4, line 978,
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Barequet/barequet2.tex>.
-/
theorem lunnon_fixed_polycube_dimension_decomposition
    (d n : ℕ) (hn : 1 < n) :
    fixedPolycubeCount d n =
      Finset.sum (Finset.Ico 1 n) (fun i => Nat.choose d i * properFixedPolycubeCount n i) := by
  have hbase : fixedPolycubeCount d n =
      ∑ m ∈ Finset.range (d + 1), d.choose m * properFixedPolycubeCount n m := by
    unfold fixedPolycubeCount
    rw [card_eq_sum_fiber_aux, sum_fiber_eq_range_aux]
  have hM1 : d + 1 ≤ max (d + 1) n := Nat.le_max_left _ _
  have hM2 : n ≤ max (d + 1) n := Nat.le_max_right _ _
  have hLHS : (∑ m ∈ Finset.range (d + 1), d.choose m * properFixedPolycubeCount n m) =
      ∑ m ∈ Finset.range (max (d + 1) n), d.choose m * properFixedPolycubeCount n m := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro m hm1 hm2
      simp only [Finset.mem_range] at hm1 hm2
      have hdm : d < m := by omega
      rw [Nat.choose_eq_zero_of_lt hdm, Nat.zero_mul]
  have hRHS : (∑ i ∈ Finset.Ico 1 n, d.choose i * properFixedPolycubeCount n i) =
      ∑ m ∈ Finset.range (max (d + 1) n), d.choose m * properFixedPolycubeCount n m := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    · intro m hm1 hm2
      simp only [Finset.mem_range, Finset.mem_Ico] at hm1 hm2
      by_cases h1 : 1 ≤ m
      · have hge : n ≤ m := by
          rcases Nat.lt_or_ge m n with h | h
          · exact absurd ⟨h1, h⟩ hm2
          · exact h
        rw [vanish_DX_ge_aux n m hge, mul_zero]
      · have hm0 : m = 0 := by omega
        subst hm0
        rw [vanish_DX_zero_aux n hn, mul_zero]
  rw [hbase, hLHS, ← hRHS]

end MetaMathlibExt
end
