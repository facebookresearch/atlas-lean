/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Ring.AddAut
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-!
# Order and totient sum do not determine simplicity (Kourovka Notebook Problem 19.25)

Kourovka Notebook, Problem 19.25 (B. Curtin, G. R. Pourgholi), marked solved in the 21st issue: let
`G` and `H` be finite groups of the same order with `∑_{g ∈ G} φ(|g|) = ∑_{h ∈ H} φ(|h|)`, where `φ`
is Euler's totient function. Suppose that `G` is simple. Is `H` necessarily simple?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.25 (B. Curtin, G. R. Pourgholi).
UnsolvedMath record UM-00701573 (`KOU-19.25`), dataset ulamai/UnsolvedMath v1.8.0.

Groups are finite types (`Fintype`), element order is `orderOf`, and simplicity is
`IsSimpleGroup` (nontrivial with only trivial normal subgroups).
The counterexample consists of two groups of order 6048 with equal totient sums.
One group, `PSU(3, 3)`, is simple.

We prove the negative answer using the degree-28 permutation representation on isotropic lines.
The point stabilizer and its cosets give unique coordinates for the group elements. Two generators
of order seven and the doubly transitive action prove simplicity.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TotientSumSimplicityKourovka19Problem25Wanted

/-- **Curtin–Pourgholi question on totient sums and simplicity (Kourovka 19.25).** The statement
that for all finite groups $G$ and $H$ of the same order with
$\sum_{g \in G} \varphi(|g|) = \sum_{h \in H} \varphi(|h|)$, where $|g|$ is the order of $g$ and
$\varphi$ is Euler's totient function, if $G$ is simple then $H$ is simple. -/
def sameOrderTotientSumSimple : Prop :=
  ∀ (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H],
    Fintype.card G = Fintype.card H →
    ∑ g : G, Nat.totient (orderOf g) = ∑ h : H, Nat.totient (orderOf h) →
    IsSimpleGroup G → IsSimpleGroup H

private abbrev Point := Fin 28
private abbrev Perm := Equiv.Perm Point

-- Write F₉ as F₃[ι] with ι² = -1. The finite isotropic points have homogeneous
-- coordinates (b,a,1), where Tr(b) = -a * conjugate(a). Encode a point by
-- 9 Im(a) + 3 Re(a) + Im(b). Point 27 is the line spanned by (1,0,0).
private def pointOf (re im height : ℕ) : Point :=
  Fin.ofNat 28 (9 * (im % 3) + 3 * (re % 3) + height % 3)

-- The translation (c,d) sends (a,b) to (c+a, d+b-conjugate(c)*a).
private def translate (i : Fin 27) (p : Point) : Point :=
  if p = 27 then 27 else
    let c := i.val / 3 % 3
    let d := i.val / 9
    let x := p.val / 3 % 3
    let y := p.val / 9
    pointOf (c + x) (d + y) (i.val % 3 + p.val % 3 + d * x + 6 - c * y)

-- The diagonal element indexed by s sends (a,b) to (s*a/Norm(s), Norm(s)*b).
-- Each nonzero norm in F₃ is its own inverse.
private def dilate (j : Fin 8) (p : Point) : Point :=
  if p = 27 then 27 else
    let c := (j.val + 1) % 3
    let d := (j.val + 1) / 3
    let norm := (c * c + d * d) % 3
    let x := p.val / 3 % 3
    let y := p.val / 9
    pointOf (norm * (c * x + 6 - d * y)) (norm * (c * y + d * x)) (norm * (p.val % 3))

-- Store the images in five-bit digits for repeated permutation composition.
private def packRow (f : Point → Point) : ℕ :=
  (List.finRange 28).foldr (fun p acc => (f p).val + 32 * acc) 0

private def atPoint (row : ℕ) (p : Point) : Point :=
  Fin.ofNat 28 ((row >>> (5 * p.val)) % 32)

private def translationRows : Array ℕ := Array.ofFn fun i : Fin 27 => packRow (translate i)
private def dilationRows : Array ℕ := Array.ofFn fun j : Fin 8 => packRow (dilate j)

-- In the same coordinates W interchanges the first and last homogeneous coordinates
-- and negates the middle one.
private def swapRow : ℕ := packRow fun p =>
  (#[27, 2, 1, 6, 22, 14, 3, 16, 26, 18, 13, 17, 12, 10, 5, 15, 7, 11, 9, 25, 23,
    21, 4, 20, 24, 19, 8, 0] : Array Point)[p.val]!

private def uInv : Array ℕ := #[
  0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22,
  9, 11, 10, 15, 17, 16, 12, 14, 13]
private def tInv : Array ℕ := #[0, 1, 5, 4, 3, 2, 7, 6]

private def uMap (i : Fin 27) := atPoint translationRows[i.val]!
private def tMap (j : Fin 8) := atPoint dilationRows[j.val]!

private def U (i : Fin 27) : Perm where
  toFun := uMap i
  invFun := uMap (Fin.ofNat 27 uInv[i.val]!)
  left_inv := (by decide +kernel : ∀ i x, uMap (Fin.ofNat 27 uInv[i.val]!) (uMap i x) = x) i
  right_inv := (by decide +kernel : ∀ i x, uMap i (uMap (Fin.ofNat 27 uInv[i.val]!) x) = x) i

private def T (j : Fin 8) : Perm where
  toFun := tMap j
  invFun := tMap (Fin.ofNat 8 tInv[j.val]!)
  left_inv := (by decide +kernel : ∀ j x, tMap (Fin.ofNat 8 tInv[j.val]!) (tMap j x) = x) j
  right_inv := (by decide +kernel : ∀ j x, tMap j (tMap (Fin.ofNat 8 tInv[j.val]!) x) = x) j

private def W : Perm where
  toFun := atPoint swapRow
  invFun := atPoint swapRow
  left_inv := by decide +kernel
  right_inv := by decide +kernel

-- Representatives for the image of infinity, followed in form by a translation and a dilation.
private def R (p : Point) : Perm := if h : p.val < 27 then U ⟨p.val, h⟩ * W else 1
private abbrev Coord := Point × Fin 27 × Fin 8
private def form (c : Coord) : Perm := R c.1 * (U c.2.1 * T c.2.2)

-- The torus acts freely on the orbit of point 3.
private def torusIndex (p : Point) : Fin 8 :=
  (#[0, 0, 1, 2, 7, 6, 5, 4, 3] : Array (Fin 8))[p.val / 3]?.getD 0

private def coords (g : Perm) : Coord :=
  let p := g 27
  let b := (R p)⁻¹ * g
  let u := Fin.ofNat 27 (b 0).val
  (p, u, torusIndex (((U u)⁻¹ * b) 3))

private def gen (b : Bool) : Perm := if b then form (0, 3, 4) else form (0, 3, 2)
private def groupG : Subgroup Perm := Subgroup.closure (Set.range gen)

private theorem gen_mem (b : Bool) : gen b ∈ groupG :=
  Subgroup.subset_closure ⟨b, rfl⟩

-- Read a binary word from its low end, with the leading 1 denoting the empty word.
private def word : ℕ → ℕ → Perm
  | 0, _ => 1
  | k + 1, m => if m < 2 then 1 else gen (m % 2 == 1) * word k (m / 2)

private theorem word_mem (k m : ℕ) : word k m ∈ groupG := by
  induction k generalizing m with
  | zero => exact groupG.one_mem
  | succ k ih =>
    simp only [word]
    split
    · exact groupG.one_mem
    · exact groupG.mul_mem (gen_mem _) (ih _)

-- Words in the two generators witnessing membership of each translation and dilation.
private def translationWords : Array ℕ := #[
  1, 35610, 30058, 803, 5132, 11837, 21368, 18831, 6720, 38637, 15321, 2077,
  1945, 7402, 5030, 4255, 6164, 5129, 18022, 14814, 2543, 8088, 4639, 738,
  1852, 7513, 1003]
private def dilationWords : Array ℕ := #[
  1, 57, 1321, 192, 191, 5311, 41, 4436]

private theorem u_mem (i : Fin 27) : U i ∈ groupG := by
  have eqn : ∀ i : Fin 27, ∀ x : Point, U i x = word 16 translationWords[i.val]! x := by
    decide +kernel
  rw [Equiv.ext (eqn i)]
  exact word_mem _ _

private theorem t_mem (j : Fin 8) : T j ∈ groupG := by
  have eqn : ∀ j : Fin 8, ∀ x : Point, T j x = word 16 dilationWords[j.val]! x := by
    decide +kernel
  rw [Equiv.ext (eqn j)]
  exact word_mem _ _

private theorem w_mem : W ∈ groupG := by
  have eqn : ∀ x : Point, W x = word 16 15425 x := by decide +kernel
  rw [Equiv.ext eqn]
  exact word_mem _ _

private theorem r_mem (p : Point) : R p ∈ groupG := by
  dsimp [R]
  split
  · exact groupG.mul_mem (u_mem _) w_mem
  · exact groupG.one_mem

private theorem form_mem (c : Coord) : form c ∈ groupG :=
  groupG.mul_mem (r_mem _) (groupG.mul_mem (u_mem _) (t_mem _))

private def uProd (i k : Fin 27) : Fin 27 := Fin.ofNat 27 (U i k.castSucc).val
private def tAct (j : Fin 8) (k : Fin 27) : Fin 27 := Fin.ofNat 27 (T j k.castSucc).val
private def tProd (i j : Fin 8) : Fin 8 := torusIndex (T i (T j 3))

private theorem u_mul (i k : Fin 27) : U i * U k = U (uProd i k) := by
  apply Equiv.ext
  exact (by decide +kernel : ∀ i k x, U i (U k x) = U (uProd i k) x) i k

private theorem t_mul (i j : Fin 8) : T i * T j = T (tProd i j) := by
  apply Equiv.ext
  exact (by decide +kernel : ∀ i j x, T i (T j x) = T (tProd i j) x) i j

private theorem t_mul_u (j : Fin 8) (k : Fin 27) : T j * U k = U (tAct j k) * T j := by
  apply Equiv.ext
  exact (by decide +kernel : ∀ j k x, T j (U k x) = U (tAct j k) (T j x)) j k

private theorem b_mul (i k : Fin 27) (j l : Fin 8) :
    (U i * T j) * (U k * T l) = U (uProd i (tAct j k)) * T (tProd j l) := by
  rw [mul_assoc, ← mul_assoc (T j), t_mul_u, mul_assoc (U (tAct j k)), ← mul_assoc, u_mul, t_mul]

private def signedGen (s b : Bool) : Perm := if s then (gen b)⁻¹ else gen b

-- A signed generator sends each representative into the indicated coset.
private theorem gen_mul_r (s b : Bool) (p : Point) :
    signedGen s b * R p = form (coords (signedGen s b * R p)) := by
  apply Equiv.ext
  exact (by decide +kernel : ∀ s b p x, (signedGen s b * R p) x =
    form (coords (signedGen s b * R p)) x) s b p

private theorem gen_mul_form (s b : Bool) (c : Coord) :
    ∃ d, signedGen s b * form c = form d := by
  rcases c with ⟨p, k, l⟩
  generalize he : coords (signedGen s b * R p) = coord
  obtain ⟨q', i', j'⟩ := coord
  refine ⟨(q', uProd i' (tAct j' k), tProd j' l), ?_⟩
  change signedGen s b * (R p * _) = R q' * _
  rw [← mul_assoc, gen_mul_r, he]
  change (R q' * (U i' * T j')) * (U k * T l) = _
  rw [mul_assoc, b_mul]

private theorem form_one : form (27, 0, 0) = 1 := by
  apply Equiv.ext
  decide +kernel

private theorem forms_cover {g : Perm} (hg : g ∈ groupG) : ∃ c, g = form c := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨_, form_one.symm⟩
  | mul_left x hx y hy ih =>
    obtain ⟨b, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := ih
    exact gen_mul_form false b c
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨b, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := ih
    exact gen_mul_form true b c

private theorem coords_form (c : Coord) : coords (form c) = c := by
  obtain ⟨p, i, j⟩ := c
  have hp : ∀ p, R p 27 = p := by decide +kernel
  have hi : ∀ i, U i 27 = 27 := by decide +kernel
  have hj : ∀ j, T j 27 = 27 := by decide +kernel
  have hiz : ∀ i : Fin 27, U i 0 = i.castSucc := by decide +kernel
  have hjz : ∀ j, T j 0 = 0 := by decide +kernel
  have htor : ∀ j, torusIndex (T j 3) = j := by decide +kernel
  have happ : form (p, i, j) 27 = p := by
    change R p (U i (T j 27)) = p
    rw [hj, hi, hp]
  unfold coords
  simp only [happ]
  simp only [form, inv_mul_cancel_left]
  have hz : (U i * T j) 0 = i.castSucc := by
    change U i (T j 0) = i.castSucc
    rw [hjz, hiz]
  rw [hz]
  have hc : Fin.ofNat 27 i.castSucc.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hc, inv_mul_cancel_left, htor]

private noncomputable def enumerate : Coord ≃ groupG :=
  Equiv.ofBijective (fun c => ⟨form c, form_mem c⟩)
    ⟨fun a b h => (coords_form a).symm.trans ((congrArg coords (congrArg Subtype.val h)).trans
      (coords_form b)), fun g => by
        obtain ⟨c, hc⟩ := forms_cover g.property
        exact ⟨c, Subtype.ext hc.symm⟩⟩

private theorem card_g : Nat.card groupG = 6048 := by
  rw [← Nat.card_congr enumerate]
  simp [Coord, Point]

-- A representative taking (infinity, zero) to any ordered pair of distinct points.
private theorem pair_rep (p q : Point) (h : p ≠ q) :
    ∃ g : groupG, (g : Perm) 27 = p ∧ (g : Perm) 0 = q := by
  let i := Fin.ofNat 27 (((R p)⁻¹ q).val)
  refine ⟨⟨R p * U i, groupG.mul_mem (r_mem _) (u_mem _)⟩, ?_⟩
  exact (by decide +kernel : ∀ p q : Point, p ≠ q →
    let g := R p * U (Fin.ofNat 27 (((R p)⁻¹ q).val))
    g 27 = p ∧ g 0 = q) p q h

private theorem double_transitive : MulAction.IsMultiplyPretransitive groupG Point 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro p q r s hpq hrs
  obtain ⟨a, hap, haq⟩ := pair_rep p q hpq
  obtain ⟨b, hbr, hbs⟩ := pair_rep r s hrs
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · change (b : Perm) ((a : Perm).symm p) = r
    rwa [← hap, Equiv.symm_apply_apply]
  · change (b : Perm) ((a : Perm).symm q) = s
    rwa [← haq, Equiv.symm_apply_apply]

-- A nontrivial normal subgroup acts transitively. Its index therefore divides 216,
-- so the quotient kills the two generators of order seven.
private theorem simple_g : IsSimpleGroup groupG := by
  have : Nontrivial groupG := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_g]; decide)
  have := MulAction.isPreprimitive_of_is_two_pretransitive double_transitive
  constructor
  intro N hnormal
  by_cases hn : N = ⊥
  · exact Or.inl hn
  right
  have hnfix : MulAction.fixedPoints N Point ≠ Set.univ := by
    intro h
    apply hn
    apply N.eq_bot_iff_forall.mpr
    intro g hg
    apply Subtype.ext
    apply Equiv.ext
    intro p
    exact Set.eq_univ_iff_forall.mp h p ⟨g, hg⟩
  have := MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hnfix
  have horb : MulAction.orbit N (27 : Point) = Set.univ := MulAction.orbit_eq_univ N _
  have hcard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N (27 : Point))
  rw [Nat.card_prod, horb, Nat.card_univ] at hcard
  have hidx := N.index_mul_card
  rw [← hcard, ← mul_left_comm, card_g] at hidx
  have hdiv : N.index ∣ 216 := ⟨Nat.card (MulAction.stabilizer N (27 : Point)), by
    rw [show Nat.card Point = 28 by simp [Point]] at hidx
    omega⟩
  have hgen (b : Bool) : (⟨gen b, gen_mem b⟩ : groupG) ∈ N := by
    let g : groupG := ⟨gen b, gen_mem b⟩
    have h7 : g ^ 7 = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      exact (by decide +kernel : ∀ b x, (gen b ^ 7) x = x) b
    have hc : N.index.Coprime (orderOf g) :=
      (show Nat.Coprime 216 7 by decide).of_dvd hdiv (orderOf_dvd_of_pow_eq_one h7)
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hc
    change g ∈ N
    rw [← hk]
    exact N.pow_mem (N.pow_index_mem g) k
  have hle : groupG ≤ N.map groupG.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨gen b, gen_mem b⟩, hgen b, rfl⟩
  apply top_unique
  intro g _
  obtain ⟨k, hk, eqn⟩ := hle g.property
  exact Subtype.ext eqn ▸ hk

-- Search the positive exponents in increasing order. A successful search certifies the order.
private def boundedOrder {M : Type*} [Monoid M] [DecidableEq M] (x : M) (bound : ℕ) : ℕ :=
  ((List.range' 1 bound).find? fun k => decide (x ^ k = 1)).getD 0

private theorem boundedOrder_spec {M : Type*} [Monoid M] [DecidableEq M] (x : M) (bound : ℕ)
    (h : boundedOrder x bound ≠ 0) : orderOf x = boundedOrder x bound := by
  unfold boundedOrder at *
  cases he : (List.range' 1 bound).find? (fun k => decide (x ^ k = 1)) with
  | none => simp [he] at h
  | some n =>
    obtain ⟨hp, hn, hmin⟩ := List.find?_range'_eq_some.mp he
    simp only [List.mem_range'_1] at hn
    exact (orderOf_eq_iff hn.1).mpr ⟨of_decide_eq_true hp, fun m hmn hm => by
      simpa using hmin m hm hmn⟩

-- The three coordinates recovered by coords show that 27, 0 and 3 form a base:
-- only the identity in the group fixes all three points.
private def fixesBase (g : Perm) : Bool := g 27 == 27 && g 0 == 0 && g 3 == 3

private theorem fixesBase_iff {g : Perm} (hg : g ∈ groupG) : fixesBase g ↔ g = 1 := by
  constructor
  · intro h
    obtain ⟨⟨hp, hz⟩, ht⟩ : (g 27 = 27 ∧ g 0 = 0) ∧ g 3 = 3 := by simpa [fixesBase] using h
    have he : coords g = coords 1 := by
      simp only [coords, Equiv.Perm.mul_apply, hp, hz, ht, Equiv.Perm.one_apply]
    obtain ⟨c, rfl⟩ := forms_cover hg
    rw [← form_one, coords_form, coords_form] at he
    exact he ▸ form_one
  · rintro rfl
    decide

private def shortForm (flip : Bool) (i : Fin 27) (j : Fin 8) : Perm :=
  (if flip then W else 1) * (U i * T j)

private def shortOrder (flip : Bool) (i : Fin 27) (j : Fin 8) : ℕ :=
  ((List.range' 1 12).find? fun n => fixesBase (shortForm flip i j ^ n)).getD 0

private theorem order_short (flip : Bool) (i : Fin 27) (j : Fin 8) :
    orderOf (shortForm flip i j) = shortOrder flip i j := by
  let g := shortForm flip i j
  have hflip : (if flip then W else 1) ∈ groupG := by
    cases flip
    · exact groupG.one_mem
    · exact w_mem
  have hg : g ∈ groupG := groupG.mul_mem hflip (groupG.mul_mem (u_mem _) (t_mem _))
  have h : shortOrder flip i j ≠ 0 := (by decide +kernel : ∀ f i j, shortOrder f i j ≠ 0) flip i j
  unfold shortOrder at h ⊢
  change orderOf g = ((List.range' 1 12).find? fun n => fixesBase (g ^ n)).getD 0
  cases he : (List.range' 1 12).find? (fun n => fixesBase (g ^ n)) with
  | none => exact (h (by exact congrArg (·.getD 0) he)).elim
  | some n =>
    obtain ⟨hp, hn, hmin⟩ := List.find?_range'_eq_some.mp he
    simp only [List.mem_range'_1] at hn
    apply (orderOf_eq_iff hn.1).mpr
    refine ⟨(fixesBase_iff (groupG.pow_mem hg n)).mp hp, ?_⟩
    intro m hm hpos hpow
    have hf := (fixesBase_iff (groupG.pow_mem hg m)).mpr hpow
    simpa [hf] using hmin m hpos hm

private def formOrder (c : Coord) : ℕ :=
  if h : c.1.val < 27 then shortOrder true (uProd c.2.1 (tAct c.2.2 ⟨c.1.val, h⟩)) c.2.2
  else shortOrder false c.2.1 c.2.2

-- Conjugate away the first translation in the nontrivial Bruhat cell.
private theorem order_form (c : Coord) : orderOf (form c) = formOrder c := by
  obtain ⟨p, i, j⟩ := c
  unfold formOrder form R
  split
  next h =>
    let k : Fin 27 := ⟨p.val, h⟩
    rw [← order_short]
    apply SemiconjBy.orderOf_eq ((U k)⁻¹)
    change (U k)⁻¹ * (U k * W * (U i * T j)) = W * (U (uProd i (tAct j k)) * T j) * (U k)⁻¹
    rw [← u_mul, mul_assoc (U i), ← t_mul_u]
    group
  next h =>
    simpa [shortForm] using order_short false i j

private theorem uProd_bijective (k : Fin 27) : Function.Bijective (uProd · k) := by
  apply Finite.injective_iff_bijective.mp
  intro i i' h
  have hg := congrArg U h
  simp only [← u_mul, mul_right_cancel_iff] at hg
  have hz : ∀ i : Fin 27, U i 0 = i.castSucc := by decide +kernel
  exact Fin.castSucc_injective _ (by simpa only [hz] using DFunLike.congr_fun hg 0)

private noncomputable instance fintypeG : Fintype groupG := Fintype.ofEquiv Coord enumerate

private theorem sum_g : ∑ g : groupG, Nat.totient (orderOf g) = 23984 := by
  rw [← enumerate.sum_comp (fun g : groupG => Nat.totient (orderOf g))]
  change ∑ c : Coord, Nat.totient (orderOf (⟨form c, form_mem c⟩ : groupG)) = _
  simp only [Subgroup.orderOf_mk, order_form, Fintype.sum_prod_type]
  have row (p : Point) : ∑ i : Fin 27, ∑ j : Fin 8, Nat.totient (formOrder (p, i, j)) =
      ∑ i : Fin 27, ∑ j : Fin 8, Nat.totient (shortOrder (p.val < 27) i j) := by
    unfold formOrder
    by_cases h : p.val < 27
    · simp only [h, dite_true, decide_true]
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (uProd_bijective (tAct j ⟨p.val, h⟩)).sum_comp
        (fun i => Nat.totient (shortOrder true i j))
    · simp [h]
  simp_rw [row]
  have subtotal (f : Bool) : (∑ i : Fin 27, ∑ j : Fin 8, Nat.totient (shortOrder f i j)) =
      (if f then 862 else 710) := by
    cases f <;> decide +kernel
  simp_rw [subtotal]
  decide +kernel

private abbrev C6 := Multiplicative (ZMod 6)
private abbrev S4 := Equiv.Perm (Fin 4)

-- The Frobenius group acts by affine transformations of the field with seven elements.
private abbrev affineAction : (ZMod 7)ˣ →* MulAut (Multiplicative (ZMod 7)) :=
  (MulAutMultiplicative (ZMod 7)).symm.toMonoidHom.comp AddAut.mulLeft
private abbrev F42 := Multiplicative (ZMod 7) ⋊[affineAction] (ZMod 7)ˣ
private abbrev GroupH := C6 × S4 × F42

private instance fintypeF42 : Fintype F42 :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

-- Enumerate permutations directly when computing the finite sum.
private local instance fintypeS4 : Fintype S4 := fintypePerm

private theorem card_h : Nat.card GroupH = 6048 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_multiplicative, ZMod.card]
  decide +kernel

private theorem not_simple_h : ¬ IsSimpleGroup GroupH := by
  intro hs
  let f := MonoidHom.snd C6 (S4 × F42)
  rcases hs.eq_bot_or_eq_top_of_normal f.ker with h | h
  · have he := f.ker_eq_bot_iff.mp h (a₁ := (Multiplicative.ofAdd 1, 1)) (a₂ := 1) rfl
    exact (by decide : Multiplicative.ofAdd (1 : ZMod 6) ≠ 1) (congrArg Prod.fst he)
  · have he := DFunLike.congr_fun (MonoidHom.ker_eq_top_iff.mp h)
      (1, Equiv.swap 0 1, 1)
    exact (by decide : (Equiv.swap 0 1 : S4) 0 ≠ 0)
      (congrArg (fun z : S4 × F42 => z.1 0) he)

-- Orders in a direct product are least common multiples of the orders in its factors.
set_option maxRecDepth 4096 in
private theorem sum_h : ∑ h : GroupH, Nat.totient (orderOf h) = 23984 := by
  have hc (x : C6) := boundedOrder_spec x 6 ((by decide +kernel : ∀ x : C6, boundedOrder x 6 ≠ 0) x)
  have hs (x : S4) := boundedOrder_spec x 4 ((by decide +kernel : ∀ x : S4, boundedOrder x 4 ≠ 0) x)
  have hf (x : F42) :=
    boundedOrder_spec x 7 ((by decide +kernel : ∀ x : F42, boundedOrder x 7 ≠ 0) x)
  change (∑ h : C6 × S4 × F42, Nat.totient (orderOf h)) = _
  simp only [Fintype.sum_prod_type, Prod.orderOf_mk, hc, hs, hf]
  decide +kernel

/--
**Order and totient sum do not determine simplicity (Kourovka 19.25).** There are finite groups
$G$ and $H$ of the same order with $\sum_{g \in G} \varphi(|g|) = \sum_{h \in H} \varphi(|h|)$,
where $|g|$ is the order of $g$ and $\varphi$ is Euler's totient function, such that $G$ is
simple and $H$ is not simple. So the Curtin–Pourgholi question has a negative answer.

Van Doorn, Judin, Monticone and Morrison (Theorem 4.1) take for $G$ the projective special
unitary group $\mathrm{PSU}(3, 3)$, which is simple of order $6048$, and
$H = C_6 \times S_4 \times F$, where $C_6$ is the cyclic group of order $6$, $S_4$ is the symmetric
group on four letters and $F$ is the Frobenius group of order $42$; both totient sums equal
$23984$.

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 19.25 (B. Curtin, G. R. Pourgholi); resolution: P.
Monticone, Kourovka Notebook Problem 19.25, solution note (2026); W. van Doorn, E. Judin, P.
Monticone and D. Morrison, On Some Problems from the Kourovka Notebook, preprint, arXiv:2607.17477
(2026), Section 4, Theorem 4.1 with Lemma 4.2 (G = PSU(3, 3) is simple, by Iwasawa's criterion, of
order 6048 with totient sum 23984) and Lemma 4.3 (H = C₆ × S₄ × F, F the Frobenius group of order
42, has the same order and totient sum and is not simple); the solution was found and verified in
Lean by the AI system Aristotle (abstract and Appendix A); the Kourovka Notebook (21st issue) marks
19.25 solved: No, it need not be (AI solution confirmed by GAP), https://arxiv.org/abs/2607.17477.
-/
theorem sameOrderTotientSumSimple_refuted : ¬ sameOrderTotientSumSimple := by
  intro h
  apply not_simple_h
  apply h groupG GroupH
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_g, card_h]
  · exact sum_g.trans sum_h.symm
  · exact simple_g

end MathlibExt.GroupTheory.TotientSumSimplicityKourovka19Problem25Wanted
