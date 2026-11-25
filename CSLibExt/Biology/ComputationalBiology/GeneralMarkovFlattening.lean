/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-edge flattenings of four-taxon trees

For the `κ`-state general Markov model on an unrooted binary phylogenetic tree `T` on four taxa
displaying the quartet `01|23`, each of the two splits `{0, 2} | {1, 3}` and `{0, 3} | {1, 2}`
that are not edges of `T` admits complex stochastic parameters whose leaf-distribution
flattening along that split has rank larger than `κ` (Allman and Rhodes 2006, Theorem 2 with
`λ = κ`). Since the rank-at-most-`κ` locus is algebraic in the parameters, it is then a proper
algebraic subset of the parameter space, and the tree is identified from generic parameters by
the vanishing of the `(κ + 1)`-minors of its own flattening.

Sources: E. S. Allman and J. A. Rhodes, "The identifiability of tree topology for phylogenetic
models, including covarion and mixture models", Journal of Computational Biology 13 (2006)
1101–1113, doi:10.1089/cmb.2006.13.1101, Theorem 2.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.SimpleGraph.ConnectedParent
import MathlibExt.Combinatorics.SimpleGraph.WalkPath

set_option autoImplicit false

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

section Model

/-- The edge `a – b` is directed away from the root `r`: `b` is one step farther from `r`. -/
def IsAwayFrom {V : Type} (G : SimpleGraph V) (r a b : V) : Prop :=
  G.Adj a b ∧ G.dist r b = G.dist r a + 1

open Classical in
/-- The joint distribution of the states `σ` at all vertices for the root distribution `π` and
the edge matrices `M a b` on the edges `a → b` directed away from the root `r`:
`π(σ r) ∏_{a → b} M a b (σ a) (σ b)`. -/
noncomputable def treeJoint {V K R : Type} [Fintype V] [CommSemiring R]
    (G : SimpleGraph V) (r : V) (π : K → R)
    (M : V → V → Matrix K K R) (σ : V → K) : R :=
  π (σ r) * ∏ ab ∈ Finset.univ.filter (fun ab : V × V => IsAwayFrom G r ab.1 ab.2),
    M ab.1 ab.2 (σ ab.1) (σ ab.2)

open Classical in
/-- The joint distribution of the leaf states, `φ_r(π, M)`: the probability that the leaf of each
taxon `x` has state `u x`, summing the joint distribution over the states at the other
vertices. -/
noncomputable def leafDist {V K X R : Type} [Fintype V] [Fintype K] [CommSemiring R]
    (G : SimpleGraph V) (ℓ : X → V) (r : V) (π : K → R)
    (M : V → V → Matrix K K R) (u : X → K) : R :=
  ∑ σ ∈ Finset.univ.filter (fun σ : V → K => ∀ x, σ (ℓ x) = u x), treeJoint G r π M σ

/-- Complex parameters for the root `r` satisfying the stochastic linear constraints: the root
vector sums to one and every edge matrix directed away from `r` has rows summing to one. -/
def IsComplexStochastic {V K : Type} [Fintype K] (G : SimpleGraph V)
    (r : V) (π : K → ℂ) (M : V → V → Matrix K K ℂ) : Prop :=
  ∑ i, π i = 1 ∧ ∀ a b, IsAwayFrom G r a b → ∀ i, ∑ j, M a b i j = 1

end Model

section Flattening

/-- The **flattening** of a function `P` of leaf states along the split `A | Aᶜ`: the matrix with
rows the states on `A`, columns the states off `A`, and entries `P(u, v)`. -/
def flatten {X K R : Type} [DecidableEq X] (A : Finset X) (P : (X → K) → R) :
    Matrix ({x // x ∈ A} → K) ({x // x ∉ A} → K) R :=
  fun u v => P fun x => if h : x ∈ A then u ⟨x, h⟩ else v ⟨x, h⟩

end Flattening

/-- The leaf of each taxon, as a vertex. -/
def leafOf {X : Type} (T : UnrootedBinaryTree X) (x : X) : T.V :=
  T.label x

section Helpers

private theorem dist_split_of_shortest (V : Type) (G : SimpleGraph V) (hG : G.Connected)
    (n : ℕ) : ∀ (w u : V) (q : G.Walk w u), q.length = n → n = G.dist w u →
      ∀ z ∈ q.support, G.dist w z + G.dist z u = G.dist w u := by
  induction n with
  | zero =>
    intro w u q hlen hdist z hz
    cases q with
    | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      simp [SimpleGraph.dist_self]
    | cons h q' =>
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
  | succ n ih =>
    intro w u q hlen hdist z hz
    cases q with
    | nil =>
      simp only [SimpleGraph.Walk.length_nil] at hlen
      omega
    | @cons _ w' _ h q' =>
      simp only [SimpleGraph.Walk.length_cons] at hlen
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · simp [SimpleGraph.dist_self]
      · have hle : G.dist w' u ≤ q'.length := SimpleGraph.dist_le q'
        have htri : G.dist w u ≤ G.dist w w' + G.dist w' u := hG.dist_triangle
        have hadj1 : G.dist w w' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
        have hdu' : G.dist w' u = n := by omega
        have hlen' : q'.length = n := by omega
        have ih' := ih w' u q' hlen' hdu'.symm z hz
        have htri2 : G.dist w z ≤ G.dist w w' + G.dist w' z := hG.dist_triangle
        have htri3 : G.dist w u ≤ G.dist w z + G.dist z u := hG.dist_triangle
        omega

private theorem mem_support_sideE (V : Type) (G : SimpleGraph V) (hG : G.IsTree)
    (e f x : V) (hef : G.Adj e f) (px : G.Walk x e) (hlen : px.length = G.dist x e)
    (hx : G.dist x e < G.dist x f) (z : V) (hz : z ∈ px.support) :
    G.dist z e < G.dist z f := by
  have hsplit := dist_split_of_shortest V G hG.connected _ x e px hlen rfl z hz
  have htri : G.dist x f ≤ G.dist x z + G.dist z f := hG.connected.dist_triangle
  rcases hG.dist_eq_dist_add_one_of_adj x hef with h | h
  · omega
  · omega

private theorem mem_support_sideF (V : Type) (G : SimpleGraph V) (hG : G.IsTree)
    (e f y : V) (hef : G.Adj e f) (py : G.Walk f y) (hlen : py.length = G.dist f y)
    (hy : G.dist y f < G.dist y e) (z : V) (hz : z ∈ py.support) :
    G.dist z f < G.dist z e := by
  have hsplit := dist_split_of_shortest V G hG.connected _ f y py hlen rfl z hz
  have htri : G.dist y e ≤ G.dist y z + G.dist z e := hG.connected.dist_triangle
  have hcomm1 : G.dist f z = G.dist z f := SimpleGraph.dist_comm
  have hcomm2 : G.dist z y = G.dist y z := SimpleGraph.dist_comm
  have hcomm3 : G.dist f y = G.dist y f := SimpleGraph.dist_comm
  rcases hG.dist_eq_dist_add_one_of_adj y hef with h | h
  · omega
  · omega

private theorem cross_edge (V : Type) (G : SimpleGraph V) (hG : G.IsTree)
    (e f x y : V) (hef : G.Adj e f)
    (hx : G.dist x e < G.dist x f) (hy : G.dist y f < G.dist y e)
    (hxy : G.Adj x y) : x = e ∧ y = f := by
  have hxe : G.dist x f = G.dist x e + 1 := by
    rcases hG.dist_eq_dist_add_one_of_adj x hef with h | h
    · omega
    · exact h
  have hye : G.dist y e = G.dist y f + 1 := by
    rcases hG.dist_eq_dist_add_one_of_adj y hef with h | h
    · exact h
    · omega
  have htri1 : G.dist y e ≤ G.dist y x + G.dist x e := hG.connected.dist_triangle
  have htri2 : G.dist x f ≤ G.dist x y + G.dist y f := hG.connected.dist_triangle
  have hxy1 : G.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy
  have hyx1 : G.dist y x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy.symm
  have heq : G.dist x e = G.dist y f := by omega
  obtain ⟨px, hpx_path, hpx_len⟩ := hG.connected.exists_path_of_dist x e
  obtain ⟨py, hpy_path, hpy_len⟩ := hG.connected.exists_path_of_dist f y
  have hsideE : ∀ z ∈ px.support, G.dist z e < G.dist z f :=
    fun z hz => mem_support_sideE V G hG e f x hef px hpx_len hx z hz
  have hsideF : ∀ z ∈ py.support, G.dist z f < G.dist z e :=
    fun z hz => mem_support_sideF V G hG e f y hef py hpy_len hy z hz
  have hne : e ≠ f := hef.ne
  set E : G.Walk e f := SimpleGraph.Walk.cons hef SimpleGraph.Walk.nil with hEdef
  have hEf : ∀ a ∈ E.support, a = e ∨ a = f := by
    intro a ha
    rw [hEdef] at ha
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    exact ha
  have hE_path : E.IsPath := by
    rw [hEdef, SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    intro hm
    simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    exact hne hm
  have hQ1_path : (px.append E).IsPath := by
    apply SimpleGraph.Walk.isPath_append_of_isPath hpx_path hE_path
    intro a ha1 ha2
    have hside := hsideE a ha1
    rcases hEf a ha2 with h | h
    · exact h
    · rw [h] at hside
      have h1 : G.dist f e = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef.symm
      have h0 : G.dist f f = 0 := SimpleGraph.dist_self
      exfalso
      omega
  have hP2_path : ((px.append E).append py).IsPath := by
    apply SimpleGraph.Walk.isPath_append_of_isPath hQ1_path hpy_path
    intro a ha1 ha2
    have hside := hsideF a ha2
    rw [SimpleGraph.Walk.mem_support_append_iff] at ha1
    rcases ha1 with ha1 | ha1
    · have hsideE' := hsideE a ha1
      exfalso
      omega
    · rcases hEf a ha1 with h | h
      · rw [h] at hside
        have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
        have h0 : G.dist e e = 0 := SimpleGraph.dist_self
        exfalso
        omega
      · exact h
  have hP1_path : (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    intro hm
    simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    exact hxy.ne hm
  have heqw : ((px.append E).append py) = SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil := by
    have hsub := hG.isAcyclic.subsingleton_path x y
    have h := hsub.elim (⟨_, hP2_path⟩ : G.Path x y) (⟨_, hP1_path⟩ : G.Path x y)
    exact congrArg Subtype.val h
  have hlen_eq := congrArg SimpleGraph.Walk.length heqw
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append] at hlen_eq
  have hElen : E.length = 1 := by
    rw [hEdef]
    simp [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
  have hP1len : (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil).length = 1 := by
    simp [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
  rw [hElen, hP1len, hpx_len, hpy_len] at hlen_eq
  have hxe0 : G.dist x e = 0 := by omega
  have hxx : x = e := hG.connected.dist_eq_zero_iff.mp hxe0
  have hyf0 : G.dist y f = 0 := by omega
  have hyy : y = f := hG.connected.dist_eq_zero_iff.mp hyf0
  exact ⟨hxx, hyy⟩

private theorem treeJoint_eq_zero_of_neE (V K : Type) [Fintype V] [DecidableEq K]
    (G : SimpleGraph V) (hG : G.IsTree) (e f : V) (hef : G.Adj e f)
    (c : ℂ) (M : V → V → Matrix K K ℂ)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (σ : V → K) (n : ℕ) : ∀ (w : V), G.dist w e = n → G.dist w e < G.dist w f →
      σ w ≠ σ e → treeJoint G e (fun _ => c) M σ = 0 := by
  classical
  induction n with
  | zero =>
    intro w hdist hw hne
    have hwe : w = e := hG.connected.dist_eq_zero_iff.mp hdist
    rw [hwe] at hne
    exact absurd rfl hne
  | succ n ih =>
    intro w hdist hw hne
    have hwe : w ≠ e := fun heq => hne (by rw [heq])
    obtain ⟨p, hp_adj, hp_dist⟩ := SimpleGraph.exists_parent hG.connected hwe
    have hc1 : G.dist e w = G.dist w e := SimpleGraph.dist_comm
    have hc2 : G.dist e p = G.dist p e := SimpleGraph.dist_comm
    have hdist_p : G.dist p e = n := by omega
    have hwp : G.dist w p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp_adj
    have htri_wf : G.dist w f ≤ G.dist w p + G.dist p f := hG.connected.dist_triangle
    have hside_p : G.dist p e < G.dist p f := by omega
    by_cases hσp : σ p = σ e
    · have hσne : σ p ≠ σ w := fun h => hne (h.symm.trans hσp)
      have hnef : ¬(p = e ∧ w = f) := by
        intro h
        rw [h.2] at hw
        have h1 : G.dist f e = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef.symm
        have h0 : G.dist f f = 0 := SimpleGraph.dist_self
        omega
      have hmem : (p, w) ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_adj.symm, hp_dist.symm⟩
      have hfactor : M p w (σ p) (σ w) = 0 := by
        rw [hI p w hnef]
        simp [hσne]
      have hprod : ∏ ab ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2),
          M ab.1 ab.2 (σ ab.1) (σ ab.2) = 0 :=
        Finset.prod_eq_zero hmem hfactor
      simp only [treeJoint, hprod, mul_zero]
    · exact ih p hdist_p hside_p hσp

private theorem treeJoint_eq_zero_of_neF (V K : Type) [Fintype V] [DecidableEq K]
    (G : SimpleGraph V) (hG : G.IsTree) (e f : V) (hef : G.Adj e f)
    (c : ℂ) (M : V → V → Matrix K K ℂ)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (σ : V → K) (n : ℕ) : ∀ (w : V), G.dist w f = n → G.dist w f < G.dist w e →
      σ w ≠ σ f → treeJoint G e (fun _ => c) M σ = 0 := by
  classical
  induction n with
  | zero =>
    intro w hdist hw hne
    have hwf : w = f := hG.connected.dist_eq_zero_iff.mp hdist
    rw [hwf] at hne
    exact absurd rfl hne
  | succ n ih =>
    intro w hdist hw hne
    have hwf : w ≠ f := fun heq => hne (by rw [heq])
    obtain ⟨p, hp_adj, hp_dist⟩ := SimpleGraph.exists_parent hG.connected hwf
    have hc1 : G.dist f w = G.dist w f := SimpleGraph.dist_comm
    have hc2 : G.dist f p = G.dist p f := SimpleGraph.dist_comm
    have hdist_p : G.dist p f = n := by omega
    have hwp : G.dist w p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp_adj
    have htri_we : G.dist w e ≤ G.dist w p + G.dist p e := hG.connected.dist_triangle
    have hside_p : G.dist p f < G.dist p e := by omega
    have hside_w : G.dist e w = G.dist f w + 1 := by
      have hcomm : G.dist e w = G.dist w e := SimpleGraph.dist_comm
      have hcomm2 : G.dist f w = G.dist w f := SimpleGraph.dist_comm
      rcases hG.dist_eq_dist_add_one_of_adj w hef with h | h
      · omega
      · omega
    have hside_p' : G.dist e p = G.dist f p + 1 := by
      have hcomm : G.dist e p = G.dist p e := SimpleGraph.dist_comm
      have hcomm2 : G.dist f p = G.dist p f := SimpleGraph.dist_comm
      rcases hG.dist_eq_dist_add_one_of_adj p hef with h | h
      · omega
      · omega
    have hdir : G.dist e w = G.dist e p + 1 := by omega
    by_cases hσp : σ p = σ f
    · have hσne : σ p ≠ σ w := fun h => hne (h.symm.trans hσp)
      have hpe : p ≠ e := by
        intro h
        rw [h] at hside_p
        have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
        have h0 : G.dist e e = 0 := SimpleGraph.dist_self
        omega
      have hnef : ¬(p = e ∧ w = f) := fun h => hpe h.1
      have hmem : (p, w) ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_adj.symm, hdir⟩
      have hfactor : M p w (σ p) (σ w) = 0 := by
        rw [hI p w hnef]
        simp [hσne]
      have hprod : ∏ ab ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2),
          M ab.1 ab.2 (σ ab.1) (σ ab.2) = 0 :=
        Finset.prod_eq_zero hmem hfactor
      simp only [treeJoint, hprod, mul_zero]
    · exact ih p hdist_p hside_p hσp

private theorem treeJoint_pattern (V K : Type) [Fintype V] [DecidableEq K]
    (G : SimpleGraph V) (hG : G.IsTree) (e f : V) (hef : G.Adj e f)
    (c : ℂ) (M : V → V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (a b : K) (σ : V → K)
    (hσ : ∀ w, (G.dist w e < G.dist w f → σ w = a) ∧
      (G.dist w f < G.dist w e → σ w = b)) :
    treeJoint G e (fun _ => c) M σ = c * c := by
  classical
  have hmem_ef : (e, f) ∈ Finset.univ.filter
      (fun ab : V × V => IsAwayFrom G e ab.1 ab.2) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hef, ?_⟩
    have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
    have h0 : G.dist e e = 0 := SimpleGraph.dist_self
    omega
  have hprod : ∏ ab ∈ Finset.univ.filter
      (fun ab : V × V => IsAwayFrom G e ab.1 ab.2),
      M ab.1 ab.2 (σ ab.1) (σ ab.2) = M e f (σ e) (σ f) := by
    apply Finset.prod_eq_single (e, f)
    · intro xy hxy hne
      obtain ⟨x, y⟩ := xy
      show M x y (σ x) (σ y) = 1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      have hxy' : G.Adj x y ∧ G.dist e y = G.dist e x + 1 := hxy
      obtain ⟨hadj, hdir⟩ := hxy'
      have hnef : ¬(x = e ∧ y = f) := by
        intro h
        apply hne
        rw [h.1, h.2]
      have hxside : G.dist x e < G.dist x f ∨ G.dist x f < G.dist x e := by
        have hne' : G.dist x e ≠ G.dist x f := hG.dist_ne_of_adj x hef
        exact lt_or_gt_of_ne hne'
      have hyside : G.dist y e < G.dist y f ∨ G.dist y f < G.dist y e := by
        have hne' : G.dist y e ≠ G.dist y f := hG.dist_ne_of_adj y hef
        exact lt_or_gt_of_ne hne'
      have hsame : σ x = σ y := by
        rcases hxside with hxE | hxF <;> rcases hyside with hyE | hyF
        · rw [(hσ x).1 hxE, (hσ y).1 hyE]
        · obtain ⟨hxe, hyf⟩ := cross_edge V G hG e f x y hef hxE hyF hadj
          rw [hxe, hyf] at hne
          exact absurd rfl hne
        · obtain ⟨hye, hxf⟩ := cross_edge V G hG e f y x hef hyE hxF hadj.symm
          rw [hxf, hye] at hdir
          have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
          have h0 : G.dist e e = 0 := SimpleGraph.dist_self
          exfalso
          omega
        · rw [(hσ x).2 hxF, (hσ y).2 hyF]
      rw [hI x y hnef, Matrix.one_apply]
      exact ite_eq_left hsame
    · intro hcon
      exact absurd hmem_ef hcon
  have hJval : M e f (σ e) (σ f) = c := by rw [hJ]
  simp only [treeJoint, hprod, hJval]

private theorem fin4_cases (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have hmem : x ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by
    rw [← huniv]
    exact Finset.mem_univ x
  simpa using hmem

private theorem rank_of_perm (Row Col : Type) [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M' : Matrix Row Col ℂ) (φ : Row ≃ Col) (d : ℂ) (hd : d ≠ 0)
    (hM : ∀ p q, M' p q = if φ p = q then d else 0) :
    M'.rank = Fintype.card Row := by
  classical
  have hsub : M'.submatrix (Equiv.refl Row) φ = d • (1 : Matrix Row Row ℂ) := by
    funext p r
    show M' p (φ r) = (d • (1 : Matrix Row Row ℂ)) p r
    rw [hM]
    simp only [Matrix.smul_apply, smul_eq_mul]
    by_cases hpr : p = r
    · subst hpr
      rw [ite_eq_left rfl, Matrix.one_apply, ite_eq_left rfl, mul_one]
    · have hne : φ p ≠ φ r := fun h => hpr (φ.injective h)
      rw [ite_eq_right hne, Matrix.one_apply, ite_eq_right hpr, mul_zero]
  have h1 : M'.rank = (M'.submatrix (Equiv.refl Row) φ).rank := by
    rw [Matrix.rank_submatrix]
  rw [h1, hsub]
  have hd' : d ∈ nonZeroDivisors ℂ := mem_nonZeroDivisors_of_ne_zero hd
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ hd', Matrix.rank_one]

private theorem exists_edge_of_quartet (T : UnrootedBinaryTree (Fin 4))
    (hT : DisplaysQuartet T 0 1 2 3) :
    ∃ e f : T.V, T.G.Adj e f ∧
      T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f ∧
      T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f ∧
      T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e ∧
      T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e := by
  obtain ⟨A0, hA0mem, h0mem, h1mem, h2nmem, h3nmem⟩ := hT
  simp only [edgeSplits] at hA0mem
  obtain ⟨⟨p, v⟩, hmem, heq⟩ := Finset.mem_image.mp hA0mem
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hmem
  have h0 : T.G.dist (leafOf T 0) v < T.G.dist (leafOf T 0) p := by
    have : (0 : Fin 4) ∈ edgeSide T p v := heq ▸ h0mem
    simpa [edgeSide, leafOf] using this
  have h1 : T.G.dist (leafOf T 1) v < T.G.dist (leafOf T 1) p := by
    have : (1 : Fin 4) ∈ edgeSide T p v := heq ▸ h1mem
    simpa [edgeSide, leafOf] using this
  have hn2 : ¬ T.G.dist (leafOf T 2) v < T.G.dist (leafOf T 2) p := by
    intro hlt
    have : (2 : Fin 4) ∈ edgeSide T p v := by simpa [edgeSide, leafOf] using hlt
    rw [heq] at this
    exact h2nmem this
  have hn3 : ¬ T.G.dist (leafOf T 3) v < T.G.dist (leafOf T 3) p := by
    intro hlt
    have : (3 : Fin 4) ∈ edgeSide T p v := by simpa [edgeSide, leafOf] using hlt
    rw [heq] at this
    exact h3nmem this
  refine ⟨v, p, hmem.symm, h0, h1, ?_, ?_⟩
  · have hside := T.isTree.dist_eq_dist_add_one_of_adj (leafOf T 2) hmem.symm
    omega
  · have hside := T.isTree.dist_eq_dist_add_one_of_adj (leafOf T 3) hmem.symm
    omega

private theorem leafDist_eq_zero_of_not_both_eq {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : Fin 4 → K) (h : ¬(u 0 = u 1 ∧ u 2 = u 3)) :
    leafDist T.G (leafOf T) e (fun _ => c) M u = 0 := by
  simp only [leafDist]
  apply Finset.sum_eq_zero
  intro σ hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  by_cases h01 : u 0 = u 1
  · by_cases h23 : u 2 = u 3
    · exfalso
      exact h ⟨h01, h23⟩
    · have hσ2 : σ (leafOf T 2) = u 2 := hmem 2
      have hσ3 : σ (leafOf T 3) = u 3 := hmem 3
      have hne23 : σ (leafOf T 2) ≠ σ (leafOf T 3) := by
        rw [hσ2, hσ3]
        exact h23
      by_cases hf2 : σ (leafOf T 2) = σ f
      · by_cases hf3 : σ (leafOf T 3) = σ f
        · exfalso
          exact hne23 (hf2.trans hf3.symm)
        · exact treeJoint_eq_zero_of_neF T.V K T.G T.isTree e f hef c M hI σ
            (T.G.dist (leafOf T 3) f) (leafOf T 3) rfl h3F hf3
      · exact treeJoint_eq_zero_of_neF T.V K T.G T.isTree e f hef c M hI σ
          (T.G.dist (leafOf T 2) f) (leafOf T 2) rfl h2F hf2
  · have hσ0 : σ (leafOf T 0) = u 0 := hmem 0
    have hσ1 : σ (leafOf T 1) = u 1 := hmem 1
    have hne01 : σ (leafOf T 0) ≠ σ (leafOf T 1) := by
      rw [hσ0, hσ1]
      exact h01
    by_cases he0 : σ (leafOf T 0) = σ e
    · by_cases he1 : σ (leafOf T 1) = σ e
      · exfalso
        exact hne01 (he0.trans he1.symm)
      · exact treeJoint_eq_zero_of_neE T.V K T.G T.isTree e f hef c M hI σ
          (T.G.dist (leafOf T 1) e) (leafOf T 1) rfl h1E he1
    · exact treeJoint_eq_zero_of_neE T.V K T.G T.isTree e f hef c M hI σ
        (T.G.dist (leafOf T 0) e) (leafOf T 0) rfl h0E he0

private theorem leafDist_eq_mul_of_both_eq {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : Fin 4 → K) (h01 : u 0 = u 1) (h23 : u 2 = u 3) :
    leafDist T.G (leafOf T) e (fun _ => c) M u = c * c := by
  classical
  set a : K := u 0 with ha
  set b : K := u 2 with hb
  have ha1 : a = u 1 := h01
  have hb3 : b = u 3 := h23
  -- canonical state: a on E side, b on F side
  set σ₀ : T.V → K := fun w => if T.G.dist w e < T.G.dist w f then a else b with hσ₀
  have hσ₀_eq_a : ∀ w, T.G.dist w e < T.G.dist w f → σ₀ w = a := by
    intro w hw
    simp [hσ₀, hw]
  have hσ₀_eq_b : ∀ w, T.G.dist w f < T.G.dist w e → σ₀ w = b := by
    intro w hw
    have hn : ¬ T.G.dist w e < T.G.dist w f := by omega
    simp [hσ₀, hn]
  have hP : ∀ x, σ₀ (leafOf T x) = u x := by
    intro x
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · exact hσ₀_eq_a _ h0E
    · rw [hσ₀_eq_a _ h1E]
      exact ha1
    · exact hσ₀_eq_b _ h2F
    · rw [hσ₀_eq_b _ h3F]
      exact hb3
  have hσ₀_val : treeJoint T.G e (fun _ => c) M σ₀ = c * c := by
    apply treeJoint_pattern T.V K T.G T.isTree e f hef c M hJ hI a b σ₀
    intro w
    exact ⟨fun hw => hσ₀_eq_a w hw, fun hw => hσ₀_eq_b w hw⟩
  simp only [leafDist]
  rw [← hσ₀_val]
  apply Finset.sum_eq_single σ₀
  · intro σ hmem hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    by_cases hE : ∀ w, T.G.dist w e < T.G.dist w f → σ w = σ e
    · by_cases hF : ∀ w, T.G.dist w f < T.G.dist w e → σ w = σ f
      · exfalso
        apply hne
        funext w
        have hσe : σ e = a := by
          have h1 := hE (leafOf T 0) h0E
          have h2 := hmem 0
          rw [h2] at h1
          exact h1.symm
        have hσf : σ f = b := by
          have h1 := hF (leafOf T 2) h2F
          have h2 := hmem 2
          rw [h2] at h1
          exact h1.symm
        have hside : T.G.dist w e < T.G.dist w f ∨ T.G.dist w f < T.G.dist w e := by
          have hne' : T.G.dist w e ≠ T.G.dist w f := T.isTree.dist_ne_of_adj w hef
          exact lt_or_gt_of_ne hne'
        rcases hside with hwE | hwF
        · rw [hE w hwE, hσe]
          exact (hσ₀_eq_a w hwE).symm
        · rw [hF w hwF, hσf]
          exact (hσ₀_eq_b w hwF).symm
      · push Not at hF
        obtain ⟨w, hwF, hwne⟩ := hF
        exact treeJoint_eq_zero_of_neF T.V K T.G T.isTree e f hef c M hI σ
          (T.G.dist w f) w rfl hwF hwne
    · push Not at hE
      obtain ⟨w, hwE, hwne⟩ := hE
      exact treeJoint_eq_zero_of_neE T.V K T.G T.isTree e f hef c M hI σ
        (T.G.dist w e) w rfl hwE hwne
  · intro hcon
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcon
    exact False.elim (hcon hP)

private theorem leafDist_pattern {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : Fin 4 → K) :
    leafDist T.G (leafOf T) e (fun _ => c) M u =
      if u 0 = u 1 ∧ u 2 = u 3 then c * c else 0 := by
  by_cases h : u 0 = u 1 ∧ u 2 = u 3
  · rw [ite_eq_left h]
    exact leafDist_eq_mul_of_both_eq T e f hef h0E h1E h2F h3F c M hJ hI u h.1 h.2
  · rw [ite_eq_right h]
    exact leafDist_eq_zero_of_not_both_eq T e f hef h0E h1E h2F h3F c M hI u h

private noncomputable def equivRowCol02 {K : Type} :
    (({x // x ∈ ({0, 2} : Finset (Fin 4))} → K) ≃
      (({x // x ∉ ({0, 2} : Finset (Fin 4))} → K))) where
  toFun := fun u ⟨x, hx⟩ =>
    if h1 : x = 1 then u ⟨0, by decide⟩
    else if h3 : x = 3 then u ⟨2, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact hx (by decide)
      · exact h1 rfl
      · exact hx (by decide)
      · exact h3 rfl)
  invFun := fun v ⟨x, hx⟩ =>
    if h0 : x = 0 then v ⟨1, by decide⟩
    else if h2 : x = 2 then v ⟨3, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact h0 rfl
      · exact (by decide : (1 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx
      · exact h2 rfl
      · exact (by decide : (3 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx)
  left_inv := fun u => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · show (if h0 : (0 : Fin 4) = 0 then _ else _) = u ⟨0, hx⟩
      simp
    · exact False.elim ((by decide : (1 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx)
    · show (if h0 : (2 : Fin 4) = 0 then _ else _) = u ⟨2, hx⟩
      have hne : (2 : Fin 4) ≠ 0 := by decide
      simp [hne]
    · exact False.elim ((by decide : (3 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx)
  right_inv := fun v => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · exact False.elim (hx (by decide))
    · show (if h1 : (1 : Fin 4) = 1 then _ else _) = v ⟨1, hx⟩
      simp
    · exact False.elim (hx (by decide))
    · show (if h1 : (3 : Fin 4) = 1 then _ else _) = v ⟨3, hx⟩
      have hne : (3 : Fin 4) ≠ 1 := by decide
      simp [hne]

private noncomputable def equivRowCol03 {K : Type} :
    (({x // x ∈ ({0, 3} : Finset (Fin 4))} → K) ≃
      (({x // x ∉ ({0, 3} : Finset (Fin 4))} → K))) where
  toFun := fun u ⟨x, hx⟩ =>
    if h1 : x = 1 then u ⟨0, by decide⟩
    else if h2 : x = 2 then u ⟨3, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact hx (by decide)
      · exact h1 rfl
      · exact h2 rfl
      · exact hx (by decide))
  invFun := fun v ⟨x, hx⟩ =>
    if h0 : x = 0 then v ⟨1, by decide⟩
    else if h3 : x = 3 then v ⟨2, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact h0 rfl
      · exact (by decide : (1 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx
      · exact (by decide : (2 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx
      · exact h3 rfl)
  left_inv := fun u => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · show (if h0 : (0 : Fin 4) = 0 then _ else _) = u ⟨0, hx⟩
      simp
    · exact False.elim ((by decide : (1 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx)
    · exact False.elim ((by decide : (2 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx)
    · show (if h0 : (3 : Fin 4) = 0 then _ else _) = u ⟨3, hx⟩
      have hne : (3 : Fin 4) ≠ 0 := by decide
      simp [hne]
  right_inv := fun v => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · exact False.elim (hx (by decide))
    · show (if h1 : (1 : Fin 4) = 1 then _ else _) = v ⟨1, hx⟩
      simp
    · show (if h1 : (2 : Fin 4) = 1 then _ else _) = v ⟨2, hx⟩
      have hne : (2 : Fin 4) ≠ 1 := by decide
      simp [hne]
    · exact False.elim (hx (by decide))

private theorem flatten_eq_of_phi02 {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : ({x // x ∈ ({0, 2} : Finset (Fin 4))} → K))
    (v : ({x // x ∉ ({0, 2} : Finset (Fin 4))} → K)) :
    (flatten ({0, 2} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      if equivRowCol02 (K := K) u = v then c * c else 0 := by
  classical
  set w : Fin 4 → K :=
    fun x => if h : x ∈ ({0, 2} : Finset (Fin 4)) then u ⟨x, h⟩ else v ⟨x, h⟩ with hw
  have hflat : (flatten ({0, 2} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      leafDist T.G (leafOf T) e (fun _ => c) M w := rfl
  rw [hflat]
  rw [leafDist_pattern T e f hef h0E h1E h2F h3F c M hJ hI w]
  have h0mem : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have h2mem : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have h1nmem : (1 : Fin 4) ∉ ({0, 2} : Finset (Fin 4)) := by decide
  have h3nmem : (3 : Fin 4) ∉ ({0, 2} : Finset (Fin 4)) := by decide
  have hw0 : w 0 = u ⟨0, h0mem⟩ := rfl
  have hw1 : w 1 = v ⟨1, h1nmem⟩ := rfl
  have hw2 : w 2 = u ⟨2, h2mem⟩ := rfl
  have hw3 : w 3 = v ⟨3, h3nmem⟩ := rfl
  have e1 : (equivRowCol02 (K := K) u) ⟨1, h1nmem⟩ = u ⟨0, h0mem⟩ := rfl
  have e3 : (equivRowCol02 (K := K) u) ⟨3, h3nmem⟩ = u ⟨2, h2mem⟩ := rfl
  have hiff : (w 0 = w 1 ∧ w 2 = w 3) ↔ equivRowCol02 (K := K) u = v := by
    constructor
    · intro ⟨h01, h23⟩
      rw [hw0, hw1] at h01
      rw [hw2, hw3] at h23
      have f1 : (equivRowCol02 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ := e1.trans h01
      have f3 : (equivRowCol02 (K := K) u) ⟨3, h3nmem⟩ = v ⟨3, h3nmem⟩ := e3.trans h23
      funext ⟨x, hx⟩
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact False.elim (hx (by decide))
      · exact f1
      · exact False.elim (hx (by decide))
      · exact f3
    · intro hφ
      have h1 : (equivRowCol02 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ :=
        congrFun hφ ⟨1, h1nmem⟩
      have h3 : (equivRowCol02 (K := K) u) ⟨3, h3nmem⟩ = v ⟨3, h3nmem⟩ :=
        congrFun hφ ⟨3, h3nmem⟩
      rw [e1] at h1
      rw [e3] at h3
      rw [hw0, hw1, hw2, hw3]
      exact ⟨h1, h3⟩
  by_cases hφ : equivRowCol02 (K := K) u = v
  · have hP : w 0 = w 1 ∧ w 2 = w 3 := hiff.mpr hφ
    rw [ite_eq_left hP, ite_eq_left hφ]
  · have hP : ¬(w 0 = w 1 ∧ w 2 = w 3) := fun h => hφ (hiff.mp h)
    rw [ite_eq_right hP, ite_eq_right hφ]

private theorem flatten_eq_of_phi03 {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : ({x // x ∈ ({0, 3} : Finset (Fin 4))} → K))
    (v : ({x // x ∉ ({0, 3} : Finset (Fin 4))} → K)) :
    (flatten ({0, 3} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      if equivRowCol03 (K := K) u = v then c * c else 0 := by
  classical
  set w : Fin 4 → K :=
    fun x => if h : x ∈ ({0, 3} : Finset (Fin 4)) then u ⟨x, h⟩ else v ⟨x, h⟩ with hw
  have hflat : (flatten ({0, 3} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      leafDist T.G (leafOf T) e (fun _ => c) M w := rfl
  rw [hflat]
  rw [leafDist_pattern T e f hef h0E h1E h2F h3F c M hJ hI w]
  have h0mem : (0 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by decide
  have h3mem : (3 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by decide
  have h1nmem : (1 : Fin 4) ∉ ({0, 3} : Finset (Fin 4)) := by decide
  have h2nmem : (2 : Fin 4) ∉ ({0, 3} : Finset (Fin 4)) := by decide
  have hw0 : w 0 = u ⟨0, h0mem⟩ := rfl
  have hw1 : w 1 = v ⟨1, h1nmem⟩ := rfl
  have hw2 : w 2 = v ⟨2, h2nmem⟩ := rfl
  have hw3 : w 3 = u ⟨3, h3mem⟩ := rfl
  have e1 : (equivRowCol03 (K := K) u) ⟨1, h1nmem⟩ = u ⟨0, h0mem⟩ := rfl
  have e2 : (equivRowCol03 (K := K) u) ⟨2, h2nmem⟩ = u ⟨3, h3mem⟩ := rfl
  have hiff : (w 0 = w 1 ∧ w 2 = w 3) ↔ equivRowCol03 (K := K) u = v := by
    constructor
    · intro ⟨h01, h23⟩
      rw [hw0, hw1] at h01
      rw [hw2, hw3] at h23
      have f1 : (equivRowCol03 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ := e1.trans h01
      have f2 : (equivRowCol03 (K := K) u) ⟨2, h2nmem⟩ = v ⟨2, h2nmem⟩ := by
        rw [e2]
        exact h23.symm.trans rfl
      funext ⟨x, hx⟩
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact False.elim (hx (by decide))
      · exact f1
      · exact f2
      · exact False.elim (hx (by decide))
    · intro hφ
      have h1 : (equivRowCol03 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ :=
        congrFun hφ ⟨1, h1nmem⟩
      have h2 : (equivRowCol03 (K := K) u) ⟨2, h2nmem⟩ = v ⟨2, h2nmem⟩ :=
        congrFun hφ ⟨2, h2nmem⟩
      rw [e1] at h1
      rw [e2] at h2
      rw [hw0, hw1, hw2, hw3]
      exact ⟨h1, h2.symm⟩
  by_cases hφ : equivRowCol03 (K := K) u = v
  · have hP : w 0 = w 1 ∧ w 2 = w 3 := hiff.mpr hφ
    rw [ite_eq_left hP, ite_eq_left hφ]
  · have hP : ¬(w 0 = w 1 ∧ w 2 = w 3) := fun h => hφ (hiff.mp h)
    rw [ite_eq_right hP, ite_eq_right hφ]

private theorem card_lt_card_row {K : Type} [Fintype K] [DecidableEq K]
    (hK : 2 ≤ Fintype.card K) (A : Finset (Fin 4)) (hAcard : A.card = 2) :
    Fintype.card K < Fintype.card ({x // x ∈ A} → K) := by
  have hsub : Fintype.card {x // x ∈ A} = 2 := by
    rw [Fintype.card_coe]
    exact hAcard
  have hrow : Fintype.card ({x // x ∈ A} → K) = (Fintype.card K) ^ 2 := by
    rw [Fintype.card_fun, hsub]
  rw [hrow]
  have hpos : 0 < Fintype.card K := by omega
  have h1 : 1 < Fintype.card K := by omega
  calc Fintype.card K = Fintype.card K * 1 := (mul_one _).symm
    _ < Fintype.card K * Fintype.card K :=
        (Nat.mul_lt_mul_left hpos).mpr h1
    _ = (Fintype.card K) ^ 2 := (pow_two _).symm

end Helpers

/-- **Non-edge flattenings of four-taxon trees have rank larger than `κ` for generic parameters**
(Allman and Rhodes 2006, Theorem 2 with `λ = κ`): for an unrooted binary phylogenetic tree `T` on
four taxa displaying the quartet `01|23`, and each of the two splits `{0, 2} | {1, 3}` and
`{0, 3} | {1, 2}` that are not edges of `T`, some complex stochastic parameters give a leaf
distribution whose flattening along that split has rank larger than `κ`, the number of states
(`2 ≤ κ`). Since the rank-at-most-`κ` locus is algebraic in the parameters, it is then a proper
algebraic subset of the parameter space, and the tree is identified from generic parameters by
the vanishing of the `(κ + 1)`-minors of its own flattening.

Source: Allman and Rhodes (2006), Theorem 2. -/
public theorem exists_card_lt_rank_flatten_nonEdge {K : Type} [Fintype K] [DecidableEq K]
    (hK : 2 ≤ Fintype.card K)
    (T : UnrootedBinaryTree (Fin 4)) (hT : DisplaysQuartet T 0 1 2 3)
    (A : Finset (Fin 4)) (hA : A = {0, 2} ∨ A = {0, 3}) :
    ∃ (r : T.V) (π : K → ℂ) (M : T.V → T.V → Matrix K K ℂ), IsComplexStochastic T.G r π M ∧
      Fintype.card K < (flatten A (leafDist T.G (leafOf T) r π M)).rank := by
  classical
  have hpos : 0 < Fintype.card K := by omega
  obtain ⟨e, f, hef, h0E, h1E, h2F, h3F⟩ := exists_edge_of_quartet T hT
  set c : ℂ := (Fintype.card K : ℂ)⁻¹ with hc
  have hcard_ne : (Fintype.card K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hpos)
  have hc_ne : c ≠ 0 := inv_ne_zero hcard_ne
  have hd_ne : c * c ≠ 0 := mul_ne_zero hc_ne hc_ne
  have hsum_c : ∑ _ : K, c = 1 := by
    have h1 : ∑ _ : K, c = (Fintype.card K : ℂ) * c := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, hc]
    exact mul_inv_cancel₀ hcard_ne
  set M : T.V → T.V → Matrix K K ℂ :=
    fun a b => if _ : a = e ∧ b = f then (fun _ _ => c) else 1 with hM
  have hJ : M e f = (fun _ _ => c) := by
    simp [hM]
    rfl
  have hI : ∀ a b : T.V, ¬(a = e ∧ b = f) → M a b = 1 := by
    intro a b h
    simp [hM, h]
  refine ⟨e, fun _ => c, M, ?_, ?_⟩
  · constructor
    · simpa using hsum_c
    · intro a b _ i
      by_cases h : a = e ∧ b = f
      · simp [hM, h]
        simpa using hsum_c
      · simp [hM, h]
        simp [Matrix.one_apply]
  · rcases hA with rfl | rfl
    · have hM : ∀ p q,
          (flatten ({0, 2} : Finset (Fin 4))
            (leafDist T.G (leafOf T) e (fun _ => c) M)) p q =
            if equivRowCol02 (K := K) p = q then c * c else 0 := by
        intro p q
        exact flatten_eq_of_phi02 T e f hef h0E h1E h2F h3F c M hJ hI p q
      have hrank : (flatten ({0, 2} : Finset (Fin 4))
          (leafDist T.G (leafOf T) e (fun _ => c) M)).rank =
          Fintype.card ({x // x ∈ ({0, 2} : Finset (Fin 4))} → K) :=
        rank_of_perm _ _ _ _ _ hd_ne hM
      rw [hrank]
      have hcard : (({0, 2} : Finset (Fin 4))).card = 2 := by decide
      exact card_lt_card_row hK _ hcard
    · have hM : ∀ p q,
          (flatten ({0, 3} : Finset (Fin 4))
            (leafDist T.G (leafOf T) e (fun _ => c) M)) p q =
            if equivRowCol03 (K := K) p = q then c * c else 0 := by
        intro p q
        exact flatten_eq_of_phi03 T e f hef h0E h1E h2F h3F c M hJ hI p q
      have hrank : (flatten ({0, 3} : Finset (Fin 4))
          (leafDist T.G (leafOf T) e (fun _ => c) M)).rank =
          Fintype.card ({x // x ∈ ({0, 3} : Finset (Fin 4))} → K) :=
        rank_of_perm _ _ _ _ _ hd_ne hM
      rw [hrank]
      have hcard : (({0, 3} : Finset (Fin 4))).card = 2 := by decide
      exact card_lt_card_row hK _ hcard

end WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted
