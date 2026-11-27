/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A counterexample to Deaconescu's totient lower bound

We refute the proposed lower bound for the order of the automorphism group using a
triangular matrix group over the field of seven elements. Conjugating by a diagonal element of
order three squares the thirty elementary generators and fixes the top entry. The orbit and
stabilizer of this element bound the number of automorphisms by `3 * 7 ^ 1130`, whereas the
group has order `3 * 7 ^ 1230`.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu). UnsolvedMath record UM-00701131 (`KOU-15.43`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut G` is `MulAut G` and `φ` is `Nat.totient`; both parts are stated for all finite groups in
`Type`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted

/-- **Deaconescu's totient lower bound conjecture (Kourovka 15.43(a)).** The statement that every
finite group $G$ satisfies $\varphi(|G|) \le |\mathrm{Aut}(G)|$, where $\varphi$ is Euler's totient
function and $\mathrm{Aut}(G)$ is the group of automorphisms of $G$. -/
def totientLeAutOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (Nat.card G).totient ≤ Nat.card (MulAut G)

/-- **Deaconescu's cyclicity conjecture (Kourovka 15.43(b)).** The statement that every finite group
$G$ with $|\mathrm{Aut}(G)| = \varphi(|G|)$ is cyclic, where $\varphi$ is Euler's totient function
and $\mathrm{Aut}(G)$ is the group of automorphisms of $G$. -/
def autOrderEqTotientImpliesCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card (MulAut G) = (Nat.card G).totient → IsCyclic G

private abbrev F := ZMod 7

private instance instPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private abbrev I := Fin 10
private abbrev V := I → F
private abbrev W := I → I → F
private abbrev Z := I → I → I → F

-- The diagonal is (1, ω⁻¹, ω, 1), where ω runs over the cube roots of unity.
private def weight (s : ZMod 3) : F := ![1, 2, 4] s

private lemma weight_add (s t : ZMod 3) : weight (s + t) = weight s * weight t := by
  decide +revert

private lemma weight_ne_zero (s : ZMod 3) : weight s ≠ 0 := by decide +revert

-- At each triple (i, j, k) this is an upper triangular 4 × 4 matrix: its successive
-- superdiagonals are (a i, b j, c k), (d i j, e j k), and (f i j k).
-- Matrix multiplication at each triple preserves these dependencies on the indices.
@[ext] private structure Tri where
  s : ZMod 3
  a : V
  b : V
  c : V
  d : W
  e : W
  f : Z

private def coordinatesEquiv : Tri ≃ (ZMod 3 × V × V × V × W × W × Z) where
  toFun x := (x.s, x.a, x.b, x.c, x.d, x.e, x.f)
  invFun | (s, a, b, c, d, e, f) => ⟨s, a, b, c, d, e, f⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance instFiniteTri : Finite Tri := Finite.of_equiv _ coordinatesEquiv.symm

private def multiply (x y : Tri) : Tri :=
  ⟨x.s + y.s, fun i ↦ y.a i + x.a i * weight (-y.s),
    fun j ↦ weight (-x.s) * y.b j + x.b j * weight y.s,
    fun k ↦ weight x.s * y.c k + x.c k,
    fun i j ↦ y.d i j + x.a i * y.b j + x.d i j * weight y.s,
    fun j k ↦ weight (-x.s) * y.e j k + x.b j * y.c k + x.e j k,
    fun i j k ↦ y.f i j k + x.a i * y.e j k + x.d i j * y.c k + x.f i j k⟩

private instance instMulTri : Mul Tri := ⟨multiply⟩

private lemma mul_eq (x y : Tri) : x * y = multiply x y := rfl

private instance instOneTri : One Tri := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

private lemma one_eq : (1 : Tri) = ⟨0, 0, 0, 0, 0, 0, 0⟩ := rfl

private def inverse (x : Tri) : Tri :=
  let a i := -(x.a i * weight x.s)
  let b j := -(x.b j)
  let c k := -(x.c k / weight x.s)
  let d i j := -(x.a i * b j + x.d i j * weight (-x.s))
  let e j k := -(x.b j * c k + x.e j k) / weight (-x.s)
  ⟨-x.s, a, b, c, d, e, fun i j k ↦ -(x.a i * e j k + x.d i j * c k + x.f i j k)⟩

private instance instInvTri : Inv Tri := ⟨inverse⟩

private lemma inv_eq (x : Tri) : x⁻¹ = inverse x := rfl

private lemma weight_zero : weight 0 = 1 := rfl

private instance instGroupTri : Group Tri := Group.ofRightAxioms
  (by
    intro x y z
    ext <;> simp [mul_eq, multiply, weight_add, add_assoc] <;> ring)
  (by
    intro x
    ext <;> simp [mul_eq, multiply, one_eq, weight_zero])
  (by
    intro x
    ext <;> simp [mul_eq, multiply, inv_eq, inverse, one_eq] <;>
      field_simp [weight_ne_zero] <;> ring)

private def diagonal (s : ZMod 3) : Tri := ⟨s, 0, 0, 0, 0, 0, 0⟩

private def entryA (v : V) : Tri := ⟨0, v, 0, 0, 0, 0, 0⟩

private def entryB (v : V) : Tri := ⟨0, 0, v, 0, 0, 0, 0⟩

private def entryC (v : V) : Tri := ⟨0, 0, 0, v, 0, 0, 0⟩

private def entryD (v : W) : Tri := ⟨0, 0, 0, 0, v, 0, 0⟩

private def entryE (v : W) : Tri := ⟨0, 0, 0, 0, 0, v, 0⟩

private def entryF (v : Z) : Tri := ⟨0, 0, 0, 0, 0, 0, v⟩

private def simpleEntry (r : Fin 3) : V → Tri := ![entryA, entryB, entryC] r

private lemma simpleEntry_add (r : Fin 3) (u v : V) :
    simpleEntry r (u + v) = simpleEntry r u * simpleEntry r v := by
  fin_cases r <;> ext <;>
    simp [simpleEntry, entryA, entryB, entryC, mul_eq, multiply, weight_zero, add_comm]

-- A row of entries belongs to a subgroup once all its single-coordinate rows do.
private def entryPreimage {M : Type*} [AddCommMonoid M] (H : Subgroup Tri) (row : M → Tri)
    (hzero : row 0 = 1) (hadd : ∀ x y, row (x + y) = row x * row y) : AddSubmonoid M where
  carrier := {x | row x ∈ H}
  zero_mem' := show row 0 ∈ H from hzero ▸ H.one_mem
  add_mem' {x y} hx hy := show row (x + y) ∈ H from (hadd x y) ▸ H.mul_mem hx hy

private lemma all_rows {M : Type*} [AddCommMonoid M] (S : AddSubmonoid (I → M))
    (h : ∀ i x, Pi.single i x ∈ S) (v : I → M) : v ∈ S := by
  rw [← Finset.univ_sum_single v]
  exact S.sum_mem fun i _ ↦ h i (v i)

private lemma simple_mem (H : Subgroup Tri) (r : Fin 3)
    (h : ∀ i, simpleEntry r (Pi.single i 1) ∈ H) (v : V) : simpleEntry r v ∈ H := by
  let S := entryPreimage H (simpleEntry r) (by fin_cases r <;> rfl) (simpleEntry_add r)
  apply all_rows S _ v
  intro i x
  have hx : x.val • (Pi.single i 1 : V) = (Pi.single i x : V) := by
    ext j
    by_cases hj : j = i <;> simp [hj, nsmul_eq_mul]
  exact hx ▸ S.nsmul_mem (h i) x.val

-- Multiplying elementary matrices in opposite orders produces a higher entry.
private lemma commutator_mem {x y z : Tri} (H : Subgroup Tri) (hx : x ∈ H) (hy : y ∈ H)
    (h : z * (y * x) = x * y) : z ∈ H :=
  (H.mul_mem_cancel_right (H.mul_mem hy hx)).mp (h ▸ H.mul_mem hx hy)

private lemma entryD_mem (H : Subgroup Tri) (hm : ∀ v, entryA v ∈ H)
    (hn : ∀ v, entryB v ∈ H) (v : W) : entryD v ∈ H := by
  let S := entryPreimage H entryD rfl (by
    intro x y
    ext <;> simp [entryD, mul_eq, multiply, weight_zero, add_comm])
  apply all_rows S _ v
  intro i w
  apply commutator_mem H (hm (Pi.single i 1)) (hn w)
  have hs (j k : I) : (Pi.single i w : W) j k = (Pi.single i 1 : V) j * w k := by
    by_cases hj : j = i <;> simp [hj]
  ext <;> simp [entryA, entryB, entryD, mul_eq, multiply, weight_zero, hs]

private lemma entryE_mem (H : Subgroup Tri) (hm : ∀ v, entryB v ∈ H)
    (hn : ∀ v, entryC v ∈ H) (v : W) : entryE v ∈ H := by
  let S := entryPreimage H entryE rfl (by
    intro x y
    ext <;> simp [entryE, mul_eq, multiply, weight_zero, add_comm])
  apply all_rows S _ v
  intro i w
  apply commutator_mem H (hm (Pi.single i 1)) (hn w)
  have hs (j k : I) : (Pi.single i w : W) j k = (Pi.single i 1 : V) j * w k := by
    by_cases hj : j = i <;> simp [hj]
  ext <;> simp [entryB, entryC, entryE, mul_eq, multiply, weight_zero, hs]

private lemma entryF_mem (H : Subgroup Tri) (hm : ∀ v, entryA v ∈ H)
    (hn : ∀ v, entryE v ∈ H) (v : Z) : entryF v ∈ H := by
  let S := entryPreimage H entryF rfl (by
    intro x y
    ext <;> simp [entryF, mul_eq, multiply, weight_zero, add_comm])
  apply all_rows S _ v
  intro i w
  apply commutator_mem H (hm (Pi.single i 1)) (hn w)
  have hs (j k l : I) : (Pi.single i w : Z) j k l = (Pi.single i 1 : V) j * w k l := by
    by_cases hj : j = i <;> simp [hj]
  ext <;> simp [entryA, entryE, entryF, mul_eq, multiply, weight_zero, hs]

private lemma generators (H : Subgroup Tri) (ht : diagonal 1 ∈ H)
    (hr : ∀ r i, simpleEntry r (Pi.single i 1) ∈ H) (x : Tri) : x ∈ H := by
  have ha := simple_mem H 0 (hr 0)
  have hb := simple_mem H 1 (hr 1)
  have hc := simple_mem H 2 (hr 2)
  have hd := entryD_mem H ha hb
  have he := entryE_mem H hb hc
  have hf := entryF_mem H ha he
  have hdiag (s : ZMod 3) : diagonal s ∈ H := by
    fin_cases s
    · exact H.one_mem
    · exact ht
    · exact H.mul_mem ht ht
  suffices h : ∀ y : Tri, y.s = 0 → y ∈ H by
    apply (H.mul_mem_cancel_right (hdiag (-x.s))).mp
    exact h _ (add_neg_cancel x.s)
  intro y hy
  have decomp : y = entryC y.c * entryE y.e * entryB y.b * entryF y.f *
      entryD y.d * entryA y.a := by
    ext <;> simp [entryA, entryB, entryC, entryD, entryE, entryF, mul_eq, multiply, weight_zero, hy]
  rw [decomp]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hc _) (he _)) (hb _))
    (hf _)) (hd _)) (ha _)

private abbrev First := V × V × V
private abbrev Lower := ZMod 3 × First × W × W

private def first (x : Tri) : First := (x.a, x.b, x.c)

private def lower (x : Tri) : Lower := (x.s, first x, x.d, x.e)

-- In the cube the top entry occurs with coefficient three.
private lemma cube_ext {x y : Tri} (hl : lower x = lower y) (h : x ^ 3 = y ^ 3) : x = y := by
  obtain ⟨s, a, b, c, d, e, f⟩ := x
  obtain ⟨s', a', b', c', d', e', f'⟩ := y
  simp only [lower, first, Prod.mk.injEq] at hl
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := hl
  congr 1
  funext i j k
  have hc := congrArg (fun z : Tri ↦ z.f i j k) h
  simp only [pow_succ, pow_zero, one_mul, mul_eq, multiply] at hc
  have hz : (3 : F) * (f i j k - f' i j k) = 0 := by linear_combination hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by decide))

private def doubles (x : Tri) : Prop := diagonal 1 * x = (x * x) * diagonal 1

private lemma doubles_simple (r : Fin 3) (v : V) : doubles (simpleEntry r v) := by
  fin_cases r <;> ext <;> simp [simpleEntry, entryA, entryB, entryC, diagonal, mul_eq, multiply,
    weight_zero, show weight 1 = 2 from rfl, show weight (-1) = 4 from rfl] <;> ring_nf
  simp [show (8 : F) = 1 from rfl]

private lemma phase_zero {x : Tri} (hx : doubles x) : x.s = 0 := by
  have h := congrArg Tri.s hx
  change 1 + x.s = x.s + x.s + 1 at h
  linear_combination -h

-- The other two superdiagonals have weights four and one. Thus the first
-- superdiagonal determines an element on which conjugation acts by squaring.
private lemma doubles_ext {x y : Tri} (hx : doubles x) (hy : doubles y)
    (h : first x = first y) : x = y := by
  have xs := phase_zero hx
  have ys := phase_zero hy
  obtain ⟨a, b, c⟩ : x.a = y.a ∧ x.b = y.b ∧ x.c = y.c := by simpa [first] using h
  have d : x.d = y.d := by
    funext i j
    have h₁ := congrArg (fun z : Tri ↦ z.d i j) hx
    have h₂ := congrArg (fun z : Tri ↦ z.d i j) hy
    simp only [diagonal, mul_eq, multiply, xs, ys, weight_zero, Pi.zero_apply, zero_mul,
      mul_zero, add_zero, zero_add, neg_zero, one_mul, mul_one, show weight 1 = 2 from rfl,
      a, b] at h₁ h₂
    have hz : (3 : F) * (x.d i j - y.d i j) = 0 := by linear_combination h₂ - h₁
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by decide))
  have e : x.e = y.e := by
    funext j k
    have h₁ := congrArg (fun z : Tri ↦ z.e j k) hx
    have h₂ := congrArg (fun z : Tri ↦ z.e j k) hy
    simp only [diagonal, mul_eq, multiply, xs, ys, weight_zero, Pi.zero_apply, zero_mul,
      mul_zero, add_zero, zero_add, neg_zero, one_mul, mul_one, show weight (-1) = 4 from rfl,
      b, c] at h₁ h₂
    have hz : (2 : F) * (x.e j k - y.e j k) = 0 := by linear_combination h₁ - h₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by decide))
  apply Tri.ext (xs.trans ys.symm) a b c d e
  funext i j k
  have h₁ := congrArg (fun z : Tri ↦ z.f i j k) hx
  have h₂ := congrArg (fun z : Tri ↦ z.f i j k) hy
  simp [diagonal, mul_eq, multiply, a, c, d, e] at h₁ h₂
  linear_combination h₁ - h₂

private abbrev Orbit := MulAction.orbit (MulAut Tri) (diagonal 1)
private abbrev Stab := MulAction.stabilizer (MulAut Tri) (diagonal 1)

private lemma orbit_bound : Nat.card Orbit ≤ Nat.card Lower := by
  apply Nat.card_le_card_of_injective (fun x : Orbit ↦ lower x.1)
  intro x y h
  have hc (z : Orbit) : z.1 ^ 3 = 1 := by
    obtain ⟨g, hg⟩ := z.2
    change g (diagonal 1) = z.1 at hg
    rw [← hg, ← map_pow]
    have ht : diagonal 1 ^ 3 = 1 := by
      rfl
    rw [ht, map_one]
  exact Subtype.ext (cube_ext h ((hc x).trans (hc y).symm))

private lemma stab_bound : Nat.card Stab ≤ Nat.card ((Fin 3 × I) → First) := by
  let gen (p : Fin 3 × I) := simpleEntry p.1 (Pi.single p.2 1)
  apply Nat.card_le_card_of_injective (fun g : Stab ↦ fun p ↦ first (g.1 (gen p)))
  intro g h heq
  have fixes (k : Stab) : k.1 (diagonal 1) = diagonal 1 := k.2
  have hd (k : Stab) (p : Fin 3 × I) : doubles (k.1 (gen p)) := by
    have hh := congrArg k.1 (doubles_simple p.1 (Pi.single p.2 1))
    simpa only [doubles, gen, map_mul, fixes] using hh
  apply Subtype.ext
  apply MulEquiv.ext
  exact generators (g.1.toMonoidHom.eqLocus h.1.toMonoidHom) ((fixes g).trans (fixes h).symm)
    (fun r i ↦ doubles_ext (hd g (r, i)) (hd h (r, i)) (congrFun heq (r, i)))

-- There are thirty simple generators. The thousand central coordinates of the group
-- occur in neither the orbit bound nor the stabilizer bound.
private lemma card_tri : Nat.card Tri = 3 * 7 ^ 1230 := by
  rw [Nat.card_congr coordinatesEquiv]
  simp only [Nat.card_prod, V, W, Z, F, I, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  simp only [← pow_mul, ← pow_add]

private lemma aut_bound : Nat.card (MulAut Tri) ≤ 3 * 7 ^ 1130 := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (MulAut Tri) (diagonal 1)),
    Nat.card_prod]
  apply (Nat.mul_le_mul orbit_bound stab_bound).trans
  simp only [Lower, First, Nat.card_prod, V, W, F, I, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  simp only [mul_assoc, ← pow_mul, ← pow_add, Nat.reduceAdd, Nat.reduceMul, le_refl]

private lemma lt_totient (m n : ℕ) (hmn : m ≤ n) : 3 * 7 ^ m < (3 * 7 ^ (n + 1)).totient := by
  rw [Nat.totient_mul ((by decide : Nat.Coprime 3 7).pow_right _),
    Nat.totient_prime_pow_succ (by decide), Nat.totient_prime (by decide : Nat.Prime 3)]
  calc
    3 * 7 ^ m ≤ 3 * 7 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hmn)
    _ < (2 * 6) * 7 ^ n := Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (by decide) _)
    _ = 2 * (7 ^ n * 6) := by ac_rfl

/--
**Deaconescu's totient lower bound conjecture fails (Kourovka 15.43(a)).** Not every finite group
$G$ satisfies $\varphi(|G|) \le |\mathrm{Aut}(G)|$: there is a finite group $G$ with
$|\mathrm{Aut}(G)| < \varphi(|G|)$, where $\varphi$ is Euler's totient function and
$\mathrm{Aut}(G)$ is the group of automorphisms of $G$.

Bray and Wilson prove more than is stated here: the ratio $|\mathrm{Aut}(G)| / \varphi(|G|)$ can be
made arbitrarily small.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.43 (M.
Deaconescu); resolution: J. N. Bray and R. A. Wilson, On the orders of automorphism groups of finite
groups, Bull. London Math. Soc. 37 (2005), no. 3, 381-385, main results (groups with |Aut G| <
φ(|G|), infinitely many non-cyclic groups with |Aut G| = φ(|G|), and |Aut G|/φ(|G|) arbitrarily
small); Kourovka Archive, Problem 15.43 (both answers negative),
https://webspace.maths.qmul.ac.uk/j.n.bray/web/Publ/AutG/.
-/
public theorem totientLeAutOrder_refuted : ¬ totientLeAutOrder := by
  intro h
  have hle := (h Tri).trans aut_bound
  rw [card_tri] at hle
  have hlt := lt_totient 1130 1229 (by decide)
  rw [show 1229 + 1 = 1230 from rfl] at hlt
  exact hlt.not_ge hle

end MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted
