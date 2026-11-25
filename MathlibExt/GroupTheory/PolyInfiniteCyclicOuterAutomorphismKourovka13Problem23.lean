/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Outer automorphisms of poly-infinite-cyclic groups (Kourovka Notebook Problem 13.23)

A group from a weighted five-cycle refutes Kourovka Notebook Problem 13.23.

Kourovka Notebook, Problem 13.23 (F. de Giovanni), marked solved in the 21st issue: let the group
`G` have a finite normal series with infinite cyclic factors. Is it true that `G` has a non-trivial
outer automorphism?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.23 (F. de Giovanni). UnsolvedMath record
UM-00700941 (`KOU-13.23`), dataset ulamai/UnsolvedMath v1.8.0.

A finite normal series consists of subgroups `1 = H₀ ≤ ⋯ ≤ Hₙ = G`, each normal in `G`, here with
infinite cyclic factors. `G` is required to be nontrivial: the trivial group has such a series (`n =
0`) and no outer automorphism. A non-trivial outer automorphism is an automorphism that is not
inner.

The proof uses the semidirect product strategy of Brescia, Ingrosso and Trombetti with a different
graph and a weighted incidence pairing. The five-cycle forces automorphisms of the first graded
piece to permute the vertex lines. The weight of absolute value three distinguishes an oriented
edge and fixes that permutation. The incidence pairing then forces a common sign, and its image
has index two in the lattice of central shifts. The square of the cyclic action supplies the
remaining central shift, and its fourth power is inner.
-/

namespace MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23Wanted

/-!
## Integral coordinates

The three coordinates record powers of the vertex generators, edge generators, and central
generator, in that order. The edge correction exchanges vertex powers in the product. The
central correction records the additional commutators made during that exchange.
-/

private abbrev V := Fin 5 → ℤ

private def src : Fin 5 → Fin 5 := ![0, 1, 2, 3, 0]
private def dst : Fin 5 → Fin 5 := ![1, 2, 3, 4, 4]
private def weight : Fin 5 → ℤ := ![-3, 1, 1, 1, 1]

private def node (i : Fin 5) : V := Pi.single i 1

private def pair (a b : V) : ℤ :=
  ∑ i, (weight i * a (src i) + a (dst i)) * b i

private def cross (a b : V) : V := fun i => -a (dst i) * b (src i)

private def bracket (a b : V) : V := cross a b - cross b a

private def chooseTwo (a : ℤ) : ℤ := a * (a - 1) / 2

private theorem twice_chooseTwo (a : ℤ) : 2 * chooseTwo a = a * (a - 1) := by
  rw [chooseTwo, mul_comm, Int.ediv_mul_cancel]
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero h) _
  · exact dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero (by omega : (a - 1) % 2 = 0)) _

private theorem chooseTwo_add (a b : ℤ) :
    chooseTwo (a + b) = chooseTwo a + chooseTwo b + a * b := by
  have h₁ := twice_chooseTwo (a + b)
  have h₂ := twice_chooseTwo a
  have h₃ := twice_chooseTwo b
  nlinarith

private theorem chooseTwo_neg (a : ℤ) : chooseTwo (-a) = chooseTwo a + a := by
  have h₁ := twice_chooseTwo (-a)
  have h₂ := twice_chooseTwo a
  nlinarith

private def correction (a b : V) : ℤ :=
  ∑ i, (weight i * a (dst i) * chooseTwo (b (src i)) +
    chooseTwo (a (dst i)) * b (src i) + a (dst i) * b (src i) * b (dst i))

private theorem pair_add_left (a b c : V) : pair (a + b) c = pair a c + pair b c := by
  rw [pair, pair, pair, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

private theorem pair_add_right (a b c : V) : pair a (b + c) = pair a b + pair a c := by
  simp [pair, mul_add, Finset.sum_add_distrib]

private theorem pair_neg_left (a b : V) : pair (-a) b = -pair a b := by
  simp only [pair, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply]
  ring

private theorem pair_neg_right (a b : V) : pair a (-b) = -pair a b := by
  simp [pair, Finset.sum_neg_distrib]

@[simp] private theorem pair_zero_left (b : V) : pair 0 b = 0 := by simp [pair]
@[simp] private theorem pair_zero_right (a : V) : pair a 0 = 0 := by simp [pair]

private theorem cross_add_left (a b c : V) : cross (a + b) c = cross a c + cross b c := by
  funext i
  simp only [cross, Pi.add_apply]
  ring

private theorem cross_add_right (a b c : V) : cross a (b + c) = cross a b + cross a c := by
  funext i
  simp only [cross, Pi.add_apply]
  ring

@[simp] private theorem cross_zero_left (b : V) : cross 0 b = 0 := by
  funext i
  simp [cross]

@[simp] private theorem cross_zero_right (a : V) : cross a 0 = 0 := by
  funext i
  simp [cross]

@[simp] private theorem chooseTwo_zero : chooseTwo 0 = 0 := by decide

@[simp] private theorem correction_zero_left (b : V) : correction 0 b = 0 := by
  simp [correction]

@[simp] private theorem correction_zero_right (a : V) : correction a 0 = 0 := by
  simp [correction]

private theorem correction_assoc (a b c : V) :
    correction a b + correction (a + b) c =
      correction b c + correction a (b + c) + pair c (cross a b) := by
  simp only [correction, pair, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, chooseTwo_add, cross]
  ring

private theorem cross_neg_neg (a b : V) : cross (-a) (-b) = cross a b := by
  funext i
  simp [cross]

@[ext] private structure N where
  x : V
  z : V
  c : ℤ

private def mulN (a b : N) : N :=
  ⟨a.x + b.x, a.z + b.z + cross a.x b.x,
    a.c + b.c + correction a.x b.x - pair b.x a.z⟩

private def invN (a : N) : N :=
  ⟨-a.x, -a.z - cross (-a.x) a.x,
    -a.c - correction (-a.x) a.x + pair a.x (-a.z - cross (-a.x) a.x)⟩

private instance instNGroup : Group N where
  mul := mulN
  one := ⟨0, 0, 0⟩
  inv := invN
  mul_assoc a b c := by
    change mulN (mulN a b) c = mulN a (mulN b c)
    have h := correction_assoc a.x b.x c.x
    simp only [mulN, add_assoc a.x b.x c.x, cross_add_left, cross_add_right,
      pair_add_left, pair_add_right, N.mk.injEq, true_and]
    constructor
    · abel
    · omega
  one_mul a := by
    change mulN ⟨0, 0, 0⟩ a = a
    cases a
    simp [mulN]
  mul_one a := by
    change mulN a ⟨0, 0, 0⟩ = a
    cases a
    simp [mulN]
  inv_mul_cancel a := by
    change mulN (invN a) a = ⟨0, 0, 0⟩
    simp only [invN, mulN, N.mk.injEq, neg_add_cancel, true_and]
    constructor <;> abel

private def X (i : Fin 5) : N := ⟨node i, 0, 0⟩
private def Z (i : Fin 5) : N := ⟨0, node i, 0⟩

@[simp] private theorem mulN_x (a b : N) : (a * b).x = a.x + b.x := rfl
@[simp] private theorem mulN_z (a b : N) : (a * b).z = a.z + b.z + cross a.x b.x := rfl
@[simp] private theorem mulN_c (a b : N) :
    (a * b).c = a.c + b.c + correction a.x b.x - pair b.x a.z := rfl
@[simp] private theorem oneN_x : (1 : N).x = 0 := rfl
@[simp] private theorem oneN_z : (1 : N).z = 0 := rfl
@[simp] private theorem oneN_c : (1 : N).c = 0 := rfl
@[simp] private theorem invN_x (a : N) : a⁻¹.x = -a.x := rfl
@[simp] private theorem invN_z (a : N) : a⁻¹.z = -a.z - cross (-a.x) a.x := rfl

/-!
## The cyclic action

The action negates the vertex and central coordinates on the graded pieces. Its edge and central
corrections make it an integral automorphism with a non-inner square.
-/

private def twist (a : V) : V := ![0, a 0, -a 0, a 0, -a 0]
private def shift (b : V) : ℤ := -b 0 + 2 * b 1 + 2 * b 2 + 2 * b 3 + 2 * b 4
private def quadratic (a : V) : ℤ := -chooseTwo (a 0) + a 0 * a 1

private theorem twist_add (a b : V) : twist (a + b) = twist a + twist b := by
  funext i
  fin_cases i <;> simp [twist, add_comm]

private theorem twist_neg (a : V) : twist (-a) = -twist a := by
  funext i
  fin_cases i <;> simp [twist]

@[simp] private theorem twist_zero : twist 0 = 0 := by
  funext i
  fin_cases i <;> simp [twist]

private theorem shift_add (a b : V) : shift (a + b) = shift a + shift b := by
  simp only [shift, Pi.add_apply]
  ring

private theorem shift_twist (a : V) : shift (twist a) = 0 := by
  simp [shift, twist]

private theorem quadratic_diff (a : V) : quadratic (-a) - quadratic a = -a 0 := by
  simp only [quadratic, Pi.neg_apply, chooseTwo_neg]
  ring

private theorem quadratic_correction (a b : V) :
    quadratic (a + b) - quadratic a - quadratic b =
      correction a b + correction (-a) (-b) - shift (cross a b) + pair b (twist a) := by
  simp [quadratic, correction, pair, shift, cross, twist, src, dst, weight,
    Fin.sum_univ_succ, chooseTwo_add, chooseTwo_neg]
  ring

private def flipN (a : N) : N :=
  ⟨-a.x, a.z + twist a.x, -a.c + shift a.z + quadratic a.x⟩

private def unflipN (a : N) : N :=
  ⟨-a.x, a.z + twist a.x, -a.c + shift a.z + quadratic (-a.x)⟩

private def α : MulAut N where
  toFun := flipN
  invFun := unflipN
  left_inv a := by
    cases a
    simp [flipN, unflipN, twist_neg, shift_add, shift_twist]
    abel
  right_inv a := by
    cases a
    simp [flipN, unflipN, twist_neg, shift_add, shift_twist]
    abel
  map_mul' a b := by
    have h := quadratic_correction a.x b.x
    rw [show flipN a * flipN b = mulN (flipN a) (flipN b) from rfl]
    simp only [mulN, flipN, mulN_x, mulN_z, mulN_c, twist_add, shift_add, cross_neg_neg,
      pair_neg_left, pair_add_right, N.mk.injEq]
    refine ⟨neg_add _ _, ?_, ?_⟩
    · abel
    · omega

private theorem alpha_sq (a : N) : α (α a) = ⟨a.x, a.z, a.c - a.x 0⟩ := by
  have h := quadratic_diff a.x
  change flipN (flipN a) = _
  simp only [flipN, neg_neg, twist_neg, add_neg_cancel_right,
    shift_add, shift_twist, add_zero, N.mk.injEq, true_and]
  omega

/-!
## Automorphisms on the graded pieces

The edge and central coordinates together form the commutator subgroup. The edge bracket and the
central pairing describe the commutators on the three graded pieces.
-/

private def liftX (a : V) : N := ⟨a, 0, 0⟩
private def liftZ (b : V) : N := ⟨0, b, 0⟩

private def Umap : Multiplicative V × Multiplicative ℤ →* N where
  toFun b := ⟨0, b.1.toAdd, b.2.toAdd⟩
  map_one' := rfl
  map_mul' a b := by
    change _ = mulN _ _
    simp [mulN]

private def central (k : ℤ) : N := ⟨0, 0, k⟩

@[simp] private theorem c_mul (k : ℤ) (a : N) :
    central k * a = ⟨a.x, a.z, k + a.c⟩ := by
  change mulN _ _ = _
  simp [central, mulN]

@[simp] private theorem mul_c (a : N) (k : ℤ) :
    a * central k = ⟨a.x, a.z, a.c + k⟩ := by
  change mulN _ _ = _
  simp [central, mulN]

private theorem x_mul_u (a b : V) (k : ℤ) : liftX a * ⟨0, b, k⟩ = ⟨a, b, k⟩ := by
  change mulN _ _ = _
  simp [liftX, mulN]

private theorem eq_sum_smul_node (a : V) : (∑ i, a i • node i) = a := by
  classical
  funext j
  simp [Finset.sum_apply, node, Pi.single_apply]

private theorem hom_kills_u {H : Type*} [CommGroup H] (f : N →* H) (b : V) (k : ℤ) :
    f ⟨0, b, k⟩ = 1 := by
  have fC : f (central 1) = 1 := by
    have h : X 1 * Z 0 = central 1 * (Z 0 * X 1) := by
      apply N.ext
      · funext j; fin_cases j <;> decide
      · funext j; fin_cases j <;> decide
      · decide
    apply mul_right_cancel (b := f (Z 0) * f (X 1))
    simpa only [map_mul, one_mul, mul_comm (f (X 1)) (f (Z 0))] using (congrArg f h).symm
  have fc (k : ℤ) : f (central k) = 1 := by
    have eq : central k = central 1 ^ k := by
      simpa [Umap, central] using Umap.map_zpow (1, Multiplicative.ofAdd 1) k
    rw [eq, map_zpow, fC, one_zpow]
  have fz (i : Fin 5) : f (Z i) = 1 := by
    have h : X (src i) * X (dst i) =
        Z i * (central (weight i + 1) * (X (dst i) * X (src i))) := by
      fin_cases i <;> apply N.ext
      all_goals first | (funext j; fin_cases j <;> decide) | decide
    apply mul_right_cancel (b := f (X (dst i)) * f (X (src i)))
    simpa only [map_mul, fc, one_mul, mul_comm (f (X (src i))) (f (X (dst i)))]
      using (congrArg f h).symm
  let g : V →+ Additive H :=
    (f.comp (Umap.comp (MonoidHom.inl (Multiplicative V) (Multiplicative ℤ)))).toAdditiveRight
  have hg : g b = 0 := by
    conv_lhs => rw [← eq_sum_smul_node b]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_zsmul, show g (node i) = 0 from fz i, smul_zero]
  change f (liftZ b) = 1 at hg
  rw [show (⟨0, b, k⟩ : N) = liftZ b * central k by simp [liftZ], map_mul, hg, fc, mul_one]

private def xHom : N →* Multiplicative V where
  toFun a := Multiplicative.ofAdd a.x
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem hom_factors_x {H : Type*} [CommGroup H] (f : N →* H) (a : N) :
    f a = f (liftX a.x) := by
  conv_lhs => rw [show a = liftX a.x * ⟨0, a.z, a.c⟩ by rw [x_mul_u]]
  rw [map_mul, hom_kills_u, mul_one]

private def xMap (β : MulAut N) : V →+ V where
  toFun a := (β (liftX a)).x
  map_zero' := by
    change (β 1).x = 0
    rw [map_one, oneN_x]
  map_add' a b := by
    change (β (liftX (a + b))).x = _
    have h := hom_factors_x (xHom.comp β.toMonoidHom) (liftX a * liftX b)
    change (β (liftX a * liftX b)).x = (β (liftX (a + b))).x at h
    rw [← h, map_mul, mulN_x]

private theorem xMap_apply_N (β : MulAut N) (a : N) : (β a).x = xMap β a.x :=
  hom_factors_x (xHom.comp β.toMonoidHom) a

private def xEquiv (β : MulAut N) : V ≃+ V where
  toFun := xMap β
  map_add' := (xMap β).map_add
  invFun := xMap β.symm
  left_inv a := by
    change xMap β.symm (β (liftX a)).x = a
    rw [← xMap_apply_N, MulEquiv.symm_apply_apply]
    rfl
  right_inv a := by
    change xMap β (β.symm (liftX a)).x = a
    rw [← xMap_apply_N, MulEquiv.apply_symm_apply]
    rfl

private theorem z_commutator (a b : N) :
    (a * b * (b * a)⁻¹).z = bracket a.x b.x := by
  simp only [bracket, mulN_z, invN_z, invN_x, mulN_x, add_comm b.x a.x]
  funext i
  simp only [cross, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, neg_neg]
  ring

private theorem bracket_node_self (a : V) (i : Fin 5) :
    bracket a (node (dst i)) i = a (src i) ∧
    bracket a (node (src i)) i = -a (dst i) := by
  fin_cases i <;> simp [bracket, cross, node, src, dst]

private theorem pair_node (b : V) :
    pair (node 0) b = -3 * b 0 + b 4 ∧
    pair (node 1) b = b 0 + b 1 ∧ pair (node 2) b = b 1 + b 2 ∧
    pair (node 3) b = b 2 + b 3 ∧ pair (node 4) b = b 3 + b 4 := by
  simp [pair, node, src, dst, weight, Pi.single_apply, Fin.sum_univ_succ]

private theorem pair_faithful (b : V) (h : ∀ a, pair a b = 0) : b = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := pair_node b
  have p0 := h (node 0)
  have p1 := h (node 1)
  have p2 := h (node 2)
  have p3 := h (node 3)
  have p4 := h (node 4)
  funext i
  fin_cases i
  · change b 0 = 0; omega
  · change b 1 = 0; omega
  · change b 2 = 0; omega
  · change b 3 = 0; omega
  · change b 4 = 0; omega

private theorem center_N (g : N) :
    (∀ a, g * a = a * g) ↔ g.x = 0 ∧ g.z = 0 := by
  refine ⟨fun h => ?_, fun ⟨hx, hz⟩ a => ?_⟩
  · have hb (a : V) : bracket g.x a = 0 := by
      change bracket g.x (liftX a).x = 0
      rw [← z_commutator g (liftX a), h, mul_inv_cancel, oneN_z]
    have hx : g.x = 0 := by
      funext j
      fin_cases j
      · simpa [src] using (bracket_node_self g.x 0).1.symm.trans
          (congrFun (hb (node (dst 0))) 0)
      · simpa [src] using (bracket_node_self g.x 1).1.symm.trans
          (congrFun (hb (node (dst 1))) 1)
      · simpa [src] using (bracket_node_self g.x 2).1.symm.trans
          (congrFun (hb (node (dst 2))) 2)
      · simpa [src] using (bracket_node_self g.x 3).1.symm.trans
          (congrFun (hb (node (dst 3))) 3)
      · simpa [dst] using (bracket_node_self g.x 3).2.symm.trans
          (congrFun (hb (node (src 3))) 3)
    refine ⟨hx, pair_faithful g.z fun a => ?_⟩
    have hc := congrArg N.c (h (liftX a))
    change (g * liftX a).c = (liftX a * g).c at hc
    simpa [hx, liftX] using hc
  · have : g = central g.c := by cases g; simp_all [central]
    rw [this, c_mul, mul_c, add_comm]

private theorem map_central (β : MulAut N) (k : ℤ) :
    (β (central k)).x = 0 ∧ (β (central k)).z = 0 := by
  apply (center_N _).mp
  intro a
  obtain ⟨b, rfl⟩ := β.surjective a
  simp only [← map_mul, c_mul, mul_c, add_comm]

private def centralHom : Multiplicative ℤ →* N :=
  Umap.comp (MonoidHom.inr (Multiplicative V) (Multiplicative ℤ))

private theorem map_central_eq (β : MulAut N) (k : ℤ) :
    β (central k) = central (k * (β (central 1)).c) := by
  obtain ⟨hx, hz⟩ := map_central β 1
  have e : β (central 1) = central (β (central 1)).c := by
    apply N.ext
    exacts [hx, hz, rfl]
  have h (l : ℤ) : central l ^ k = central (k * l) :=
    (centralHom.map_zpow (Multiplicative.ofAdd l) k).symm
  have h1 : central k = central 1 ^ k := by rw [h, mul_one]
  conv_lhs => rw [h1, map_zpow, e, h]

private theorem central_sign (β : MulAut N) :
    (β (central 1)).c = 1 ∨ (β (central 1)).c = -1 := by
  have h := β.symm_apply_apply (central 1)
  rw [map_central_eq β, map_central_eq β.symm] at h
  have hc := congrArg N.c h
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [central] using hc)

private def zMap (β : MulAut N) : V →+ V where
  toFun b := (β (liftZ b)).z
  map_zero' := by change (β 1).z = 0; rw [map_one, oneN_z]
  map_add' a b := by
    have h : liftZ (a + b) = liftZ a * liftZ b := by
      change _ = mulN _ _
      simp [liftZ, mulN]
    rw [h, map_mul, mulN_z, xMap_apply_N, xMap_apply_N]
    simp [liftZ]

private theorem zMap_apply_N (β : MulAut N) (a : N) (ha : a.x = 0) :
    (β a).z = zMap β a.z := by
  have heq : a = liftZ a.z * central a.c := by
    rw [mul_c]
    cases a
    simp_all [liftZ]
  conv_lhs => rw [heq, map_mul, map_central_eq, mul_c]
  rfl

private theorem bracket_map (β : MulAut N) (a b : V) :
    zMap β (bracket a b) = bracket (xEquiv β a) (xEquiv β b) := by
  let d := liftX a * liftX b * (liftX b * liftX a)⁻¹
  have hx : d.x = 0 := by
    simp only [d, mulN_x, invN_x]
    abel
  have hz := zMap_apply_N β d hx
  rw [z_commutator] at hz
  change (β d).z = zMap β (bracket a b) at hz
  rw [← hz]
  dsimp only [d]
  rw [map_mul, map_mul, map_inv, map_mul, z_commutator, xMap_apply_N, xMap_apply_N]
  rfl

private theorem commute_pair (a b : N) (hb : b.x = 0) :
    a * b = central (pair a.x b.z) * (b * a) := by
  rw [c_mul]
  apply N.ext
  · simp [hb]
  · simp [hb, add_comm b.z a.z]
  · simp [hb]
    abel

private theorem pair_map (β : MulAut N) (a b : V) :
    pair (xEquiv β a) (zMap β b) = pair a b * (β (central 1)).c := by
  have hb : (β (liftZ b)).x = 0 := by simp [xMap_apply_N, liftZ]
  have h := congrArg β (commute_pair (liftX a) (liftZ b) rfl)
  rw [map_mul, map_mul, map_mul, map_central_eq] at h
  change β (liftX a) * β (liftZ b) = central _ * (β (liftZ b) * β (liftX a)) at h
  rw [commute_pair (β (liftX a)) (β (liftZ b)) hb] at h
  have hc := congrArg N.c (mul_right_cancel h)
  exact hc

-- A vertex line is characterized by the edge bracket having rank two on nonzero vectors
-- of that line. The minors below certify that any vector with two nonzero coordinates has
-- rank at least three.

private def detThree (a b c : V) (i j k : Fin 5) : ℤ :=
  a i * (b j * c k - c j * b k) -
  b i * (a j * c k - c j * a k) +
  c i * (a j * b k - b j * a k)

private theorem det_linear_combinations (a b : V) (p q r s t u : ℤ) (i j k : Fin 5) :
    detThree (p • a + q • b) (r • a + s • b) (t • a + u • b) i j k = 0 := by
  simp [detThree]
  ring

private def incFirst : Fin 5 → Fin 5 := ![0, 0, 1, 2, 3]
private def incSecond : Fin 5 → Fin 5 := ![4, 1, 2, 3, 4]

private theorem bracket_node_support (i : Fin 5) (a : V) :
    bracket (node i) a =
      bracket (node i) a (incFirst i) • node (incFirst i) +
        bracket (node i) a (incSecond i) • node (incSecond i) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [bracket, node, cross, src, dst, incFirst, incSecond]

private theorem image_minor_zero (β : MulAut N) (v p q r i j k : Fin 5) :
    detThree (bracket (xEquiv β (node v)) (node p)) (bracket (xEquiv β (node v)) (node q))
      (bracket (xEquiv β (node v)) (node r)) i j k = 0 := by
  let S := xEquiv β
  have h (a : V) : bracket (S (node v)) a =
      bracket (node v) (S.symm a) (incFirst v) • zMap β (node (incFirst v)) +
      bracket (node v) (S.symm a) (incSecond v) • zMap β (node (incSecond v)) := by
    have h' := congrArg (zMap β) (bracket_node_support v (S.symm a))
    simpa only [bracket_map, show xEquiv β = S from rfl, AddEquiv.apply_symm_apply,
      map_add, map_zsmul] using h'
  rw [h, h, h]
  exact det_linear_combinations _ _ _ _ _ _ _ _ _ _ _

private theorem support_at_most_one (u : V) (h : ∀ p q r i j k : Fin 5,
    detThree (bracket u (node p)) (bracket u (node q)) (bracket u (node r)) i j k = 0)
    {i j : Fin 5} (hi : u i ≠ 0) (hj : u j ≠ 0) : i = j := by
  suffices aux : ∀ i j : Fin 5, i < j → u i = 0 ∨ u j = 0 by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim ((aux i j hlt).elim hi hj)
    · exact heq
    · exact False.elim ((aux j i hgt).elim hj hi)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [Fin.mk_lt_mk] at hij
  all_goals try (exfalso; omega)
  · have e := h 0 2 4 0 1 4
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 1 3 4 0 2 4
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 1 2 4 0 2 3
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 0 1 3 0 3 4
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 0 1 3 0 1 2
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 0 2 4 0 1 3
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 0 2 3 0 1 3
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 1 2 4 1 2 3
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 0 1 3 1 2 4
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto
  · have e := h 0 2 3 2 3 4
    simp [detThree, bracket, cross, node, src, dst, mul_eq_zero] at e
    tauto

private theorem one_coordinate (β : MulAut N) (i : Fin 5) :
    ∃ j : Fin 5, ∃ d : ℤ, d ≠ 0 ∧ xEquiv β (node i) = d • node j := by
  let u := xEquiv β (node i)
  have hn : u ≠ 0 := by
    intro h
    have he := (xEquiv β).injective (h.trans (map_zero (xEquiv β)).symm)
    simpa [node] using congrFun he i
  have hex : ∃ j, u j ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, u j, hj, ?_⟩
  funext k
  change u k = (u j • node j) k
  by_cases h : k = j
  · subst k
    simp [node]
  · have hz : u k = 0 := by
      by_contra hk
      exact h (support_at_most_one u (image_minor_zero β i) hk hj)
    simp [node, h, hz]

private theorem bracket_smul (x y : V) (a b : ℤ) :
    bracket (a • x) (b • y) = (a * b) • bracket x y := by
  funext i
  simp only [bracket, cross, Pi.smul_apply, Int.zsmul_eq_mul, Pi.sub_apply]
  ring

private theorem pair_smul (x y : V) (a b : ℤ) :
    pair (a • x) (b • y) = (a * b) * pair x y := by
  rw [pair, pair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

private def color (i j : Fin 5) : ℕ :=
  (pair (node i) (bracket (node i) (node j))).natAbs

private theorem color_rigid (σ : Fin 5 → Fin 5) (hinj : Function.Injective σ)
    (h : ∀ i j, color (σ i) (σ j) = color i j) : ∀ i, σ i = i := by
  have cert : ∀ i j : Fin 5, color i j = 3 ↔ i = 0 ∧ j = 1 := by decide
  have h01 : color (σ 0) (σ 1) = 3 := (h 0 1).trans (by decide)
  obtain ⟨h0, h1⟩ := (cert _ _).mp h01
  have cert1 : ∀ j : Fin 5, color 1 j = 1 → j = 0 ∨ j = 2 := by decide
  have cert2 : ∀ j : Fin 5, color 2 j = 1 → j = 1 ∨ j = 3 := by decide
  have cert3 : ∀ j : Fin 5, color 3 j = 1 → j = 2 ∨ j = 4 := by decide
  have h2 : σ 2 = 2 := by
    have he := (h 1 2).trans (by decide : color 1 2 = 1)
    rw [h1] at he
    exact (cert1 _ he).resolve_left (fun ht => (by decide : (2 : Fin 5) ≠ 0)
      (hinj (ht.trans h0.symm)))
  have h3 : σ 3 = 3 := by
    have he := (h 2 3).trans (by decide : color 2 3 = 1)
    rw [h2] at he
    exact (cert2 _ he).resolve_left (fun ht => (by decide : (3 : Fin 5) ≠ 1)
      (hinj (ht.trans h1.symm)))
  have h4 : σ 4 = 4 := by
    have he := (h 3 4).trans (by decide : color 3 4 = 1)
    rw [h3] at he
    exact (cert3 _ he).resolve_left (fun ht => (by decide : (4 : Fin 5) ≠ 2)
      (hinj (ht.trans h2.symm)))
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3, h4]

private theorem bracket_nodes (i : Fin 5) :
    bracket (node (src i)) (node (dst i)) = node i := by
  funext j
  fin_cases i <;> fin_cases j <;> decide

private theorem automorphism_graded (β : MulAut N) :
    (∀ a, xEquiv β a = (β (central 1)).c • a) ∧ ∀ b, zMap β b = b := by
  classical
  let S := xEquiv β
  let sign := (β (central 1)).c
  choose σ d hn hd using one_coordinate β
  have hinj : Function.Injective σ := by
    intro i j h
    by_contra hij
    have e : xEquiv β (d j • node i) = xEquiv β (d i • node j) := by
      simp only [map_zsmul, hd, h, smul_smul, mul_comm (d j) (d i)]
    have e' := congrFun (S.injective e) i
    apply hn j
    simpa [node, Pi.single_apply, hij, Ne.symm hij] using e'
  have unit (i : Fin 5) : d i = 1 ∨ d i = -1 := by
    obtain ⟨a, ha⟩ := S.surjective (node (σ i))
    have hsum := congrArg (xEquiv β) (eq_sum_smul_node a)
    change xEquiv β a = node (σ i) at ha
    rw [map_sum, ha] at hsum
    simp only [map_zsmul, hd, smul_smul] at hsum
    have hmul : a i * d i = 1 := by
      have hcoord := congrFun hsum (σ i)
      simpa [Finset.sum_apply, node, Pi.single_apply, hinj.eq_iff, eq_comm] using hcoord.symm
    exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [mul_comm] using hmul : d i * a i = 1)
  have cubic (i j : Fin 5) : d i * (d i * d j) *
      pair (node (σ i)) (bracket (node (σ i)) (node (σ j))) =
      pair (node i) (bracket (node i) (node j)) * sign := by
    simpa only [bracket_map, hd, bracket_smul, pair_smul] using
      pair_map β (node i) (bracket (node i) (node j))
  have absD (i) : (d i).natAbs = 1 := by
    rcases unit i with h | h <;> simp [h]
  have absL : sign.natAbs = 1 := by
    rcases central_sign β with h | h <;> simp [sign, h]
  have hs := color_rigid σ hinj fun i j => by
    simpa [Int.natAbs_mul, absD, absL, color] using congrArg Int.natAbs (cubic i j)
  have equal (i j : Fin 5) (h : pair (node i) (bracket (node i) (node j)) ≠ 0) :
      d j = sign := by
    have hi : d i * d i = 1 := by rcases unit i with e | e <;> simp [e]
    have e := cubic i j
    rw [hs, hs, ← mul_assoc, hi, one_mul, mul_comm _ sign] at e
    exact mul_right_cancel₀ h e
  have ds (i) : d i = sign := by
    fin_cases i
    exacts [equal 1 0 (by decide), equal 0 1 (by decide), equal 1 2 (by decide),
      equal 2 3 (by decide), equal 3 4 (by decide)]
  have hSign : sign * sign = 1 := by
    rcases central_sign β with h | h <;> simp [sign, h]
  constructor
  · intro a
    rw [← eq_sum_smul_node a]
    simp only [map_sum, map_zsmul, hd, hs, ds, smul_smul, Finset.smul_sum,
      mul_comm _ sign]
    rfl
  · have hz (i : Fin 5) : zMap β (node i) = node i := by
      rw [← bracket_nodes i, bracket_map, hd, hd, hs, hs, ds, ds, bracket_smul, hSign, one_smul]
    intro b
    have e : zMap β (∑ i, b i • node i) = ∑ i, b i • node i := by
      simp only [map_sum, map_zsmul, hz]
    simpa only [eq_sum_smul_node] using e

/-!
## The normalizer of the cyclic action modulo inner automorphisms

After adjusting the common sign, comparison with the cyclic action makes the edge correction of
an automorphism half of a conjugation. The bracket detects the parity of each vertex coordinate
of the conjugating element. The remaining central correction is a conjugation, possibly composed
with the square of the cyclic action.
-/

private theorem bracket_neg_right (a b : V) : bracket a (-b) = -bracket a b := by
  funext i
  simp only [bracket, cross, Pi.sub_apply, Pi.neg_apply]
  ring

private theorem conj_x (n a : N) : (MulAut.conj n a).x = a.x := by
  simp only [MulAut.conj_apply, mulN_x, invN_x]
  abel

private theorem conj_z (n a : N) : (MulAut.conj n a).z = a.z + bracket n.x a.x := by
  simp only [MulAut.conj_apply, mulN_z, mulN_x, invN_z, invN_x, bracket]
  funext j
  simp only [cross, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

private theorem conj_liftZ (b : V) (a : N) :
    MulAut.conj (liftZ b) a = ⟨a.x, a.z, a.c - pair a.x b⟩ := by
  change mulN (mulN (liftZ b) a) (invN (liftZ b)) = _
  simp [liftZ, mulN, invN, pair_neg_right]

private theorem dvd_of_bracket (v : V) (d : ℤ)
    (h : ∀ a : V, ∀ i, d ∣ bracket v a i) (j : Fin 5) : d ∣ v j := by
  have hs (i : Fin 5) : d ∣ v (src i) := by
    rw [← (bracket_node_self v i).1]
    exact h _ _
  have ht (i : Fin 5) : d ∣ v (dst i) := by
    rw [← dvd_neg, ← (bracket_node_self v i).2]
    exact h _ _
  fin_cases j
  exacts [hs 0, hs 1, hs 2, hs 3, ht 3]

private theorem bracket_faithful (v : V) (h : ∀ a : V, bracket v a = 0) : v = 0 := by
  funext i
  simpa using dvd_of_bracket v 0 (fun a j => by rw [h]; simp) i

private def qVector : V := ![-1, 1, -1, 1, -1]

private theorem pair_qVector (a : V) : pair a qVector = 2 * a 0 := by
  simp [pair, qVector, weight, src, dst, Fin.sum_univ_succ]
  ring

private theorem alpha_four : α ^ (4 : ℕ) = MulAut.conj (liftZ qVector) := by
  ext a : 1
  change α (α (α (α a))) = _
  rw [alpha_sq, alpha_sq, conj_liftZ, pair_qVector]
  simp only [N.mk.injEq, true_and]
  omega

private theorem alpha_sq_not_inner (n : N) : α ^ (2 : ℕ) ≠ MulAut.conj n := by
  intro h
  have eq (a : N) : α (α a) = MulAut.conj n a := congrFun (congrArg DFunLike.coe h) a
  have hx : n.x = 0 := by
    apply bracket_faithful
    intro a
    have he := congrArg N.z (eq (liftX a))
    rw [alpha_sq, conj_z] at he
    have h0 : (0 : V) = 0 + bracket n.x a := he
    simpa using h0.symm
  have hc (a : V) : pair a n.z = a 0 := by
    have hn : n = liftZ n.z * central n.c := by
      rw [mul_c]
      exact N.ext (by simpa [liftZ] using hx) rfl (by simp [liftZ])
    have he := eq (liftX a)
    conv_rhs at he => rw [hn, map_mul, MulAut.mul_apply]
    have hC : MulAut.conj (central n.c) (liftX a) = liftX a := by
      have e := (center_N (central n.c)).mpr ⟨rfl, rfl⟩ (liftX a)
      rw [MulAut.conj_apply, e, mul_assoc, mul_inv_cancel, mul_one]
    rw [hC, conj_liftZ, alpha_sq] at he
    exact sub_right_inj.mp (congrArg N.c he).symm
  obtain ⟨p0, p1, p2, p3, p4⟩ := pair_node n.z
  have e0 : pair (node 0) n.z = 1 := hc (node 0)
  have e1 : pair (node 1) n.z = 0 := hc (node 1)
  have e2 : pair (node 2) n.z = 0 := hc (node 2)
  have e3 : pair (node 3) n.z = 0 := hc (node 3)
  have e4 : pair (node 4) n.z = 0 := hc (node 4)
  omega

private theorem beta_z_formula (β : MulAut N) (a : N) :
    (β a).z = a.z + (β (liftX a.x)).z := by
  conv_lhs => rw [show a = liftX a.x * ⟨0, a.z, a.c⟩ by rw [x_mul_u]]
  rw [map_mul, mulN_z, xMap_apply_N β ⟨0, a.z, a.c⟩, zMap_apply_N β ⟨0, a.z, a.c⟩ rfl]
  rw [(automorphism_graded β).2]
  change _ + a.z + cross _ (xMap β 0) = _
  simp [add_comm]

private theorem pure_central (β : MulAut N) (hx : ∀ a, (β a).x = a.x)
    (hz : ∀ a, (β a).z = a.z) :
    ∃ b : V, ∃ k : ℕ, β = MulAut.conj (liftZ b) * α ^ (2 * k) := by
  let f : N →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd ((β a).c - a.c)
      map_one' := by rw [map_one, oneN_c, sub_self]; rfl
      map_mul' := fun a b => by
        change (β (a * b)).c - (a * b).c = (β a).c - a.c + ((β b).c - b.c)
        rw [map_mul]
        simp only [mulN_c, hx, hz]
        abel }
  let r : V →+ ℤ :=
    { toFun := fun a => (f (liftX a)).toAdd
      map_zero' := by change (f 1).toAdd = 0; rw [map_one]; rfl
      map_add' := fun a b => by
        have h := hom_factors_x f (liftX a * liftX b)
        rw [map_mul] at h
        exact (congrArg Multiplicative.toAdd h).symm }
  have hR (a : N) : (β a).c = a.c + r a.x := by
    have h := congrArg Multiplicative.toAdd (hom_factors_x f a)
    change (β a).c - a.c = r a.x at h
    omega
  let k : ℤ := (r (node 0) + r (node 1) + r (node 2) + r (node 3) + r (node 4)) % 2
  let c0 := -r (node 0) - k
  let c1 := -r (node 1)
  let c2 := -r (node 2)
  let c3 := -r (node 3)
  let c4 := -r (node 4)
  let b0 := (c4 - c3 + c2 - c1 - c0) / 2
  let b1 := c1 - b0
  let b2 := c2 - b1
  let b3 := c3 - b2
  let b4 := c4 - b3
  let b : V := ![b0, b1, b2, b3, b4]
  have hRnode (a : V) : r a = ∑ i, a i * r (node i) := by
    conv_lhs => rw [← eq_sum_smul_node a]
    simp only [map_sum, map_zsmul, Int.zsmul_eq_mul]
  have hPair (a : V) : pair a b = -r a - k * a 0 := by
    have h0 : -3 * b0 + b4 = c0 := by dsimp [b4, b3, b2, b1, b0, c0, c1, c2, c3, c4, k]; omega
    have h1 : b0 + b1 = c1 := by dsimp [b1]; omega
    have h2 : b1 + b2 = c2 := by dsimp [b2]; omega
    have h3 : b2 + b3 = c3 := by dsimp [b3]; omega
    have h4 : b3 + b4 = c4 := by dsimp [b4]; omega
    rw [hRnode]
    simp [pair, b, weight, src, dst, Fin.sum_univ_succ]
    linear_combination a 0 * h0 + a 1 * h1 + a 2 * h2 + a 3 * h3 + a 4 * h4
  have hk : k = 0 ∨ k = 1 := Int.emod_two_eq_zero_or_one _
  rcases hk with h | h
  · refine ⟨b, 0, ?_⟩
    ext a : 1
    change β a = MulAut.conj (liftZ b) a
    rw [conj_liftZ, hPair, h]
    apply N.ext
    · exact hx a
    · exact hz a
    · simp only [hR a]
      ring
  · refine ⟨b, 1, ?_⟩
    ext a : 1
    change β a = MulAut.conj (liftZ b) (α (α a))
    rw [alpha_sq, conj_liftZ]
    change β a = ⟨a.x, a.z, a.c - a.x 0 - pair a.x b⟩
    rw [hPair, h]
    apply N.ext
    · exact hx a
    · exact hz a
    · simp only [hR a]
      ring

@[simp] private theorem alpha_x (a : N) : (α a).x = -a.x := rfl
@[simp] private theorem alpha_z (a : N) : (α a).z = a.z + twist a.x := rfl
@[simp] private theorem alpha_inv_x (a : N) : (α⁻¹ a).x = -a.x := rfl
@[simp] private theorem alpha_inv_z (a : N) : (α⁻¹ a).z = a.z + twist a.x := rfl

private theorem alpha_R : α (liftZ qVector) = liftZ qVector * central 1 := by
  rw [mul_c]
  change flipN (liftZ qVector) = _
  simp [flipN, liftZ, shift, qVector, quadratic]

private theorem alpha_Rinv : α (liftZ qVector)⁻¹ = (liftZ qVector)⁻¹ * central (-1) := by
  rw [map_inv, alpha_R, mul_inv_rev]
  change _ = (liftZ qVector)⁻¹ * (central 1)⁻¹
  exact (center_N ((central 1)⁻¹)).mpr (by simp [central]) _

private theorem normalizer_positive (β γ : MulAut N) (n : N)
    (hγ : γ = α ∨ γ = α⁻¹)
    (hx : ∀ a : N, (β a).x = a.x)
    (h : ∀ a : N, β (α a) = MulAut.conj n (γ (β a))) :
    ∃ m : N, ∃ k : ℕ, β = MulAut.conj m * α ^ k := by
  let b (a : V) : V := (β (liftX a)).z
  have bz (a : N) : (β a).z = a.z + b a.x := beta_z_formula β a
  have bneg (a : V) : b (-a) = -b a := by
    have e := congrArg N.z (β.map_inv (liftX a))
    rw [bz ((liftX a)⁻¹), invN_z, invN_z, hx, invN_x] at e
    change 0 - cross (-a) a + b (-a) = -b a - cross (-a) a at e
    abel_nf at e ⊢
    exact add_left_cancel e
  have gxz (a : N) : (γ a).x = -a.x ∧ (γ a).z = a.z + twist a.x := by
    rcases hγ with rfl | rfl <;> exact ⟨rfl, rfl⟩
  have doubled (a : V) : (2 : ℤ) • b a = bracket n.x a := by
    have e := congrArg N.z (h (liftX a))
    change (β (α (liftX a))).z = (MulAut.conj n (γ (β (liftX a)))).z at e
    rw [bz (α (liftX a)), conj_z, (gxz _).1, (gxz _).2, alpha_x, alpha_z,
      hx, bz (liftX a), bracket_neg_right, bneg] at e
    have e' : twist a + -b a = b a + twist a + -bracket n.x a := by
      simpa only [liftX, zero_add] using e
    funext i
    have ei := congrFun e' i
    change twist a i + -(b a i) = b a i + twist a i + -(bracket n.x a i) at ei
    change 2 * b a i = bracket n.x a i
    omega
  have heven (i : Fin 5) : (2 : ℤ) ∣ n.x i := by
    apply dvd_of_bracket
    intro a j
    refine ⟨b a j, ?_⟩
    rw [← doubled a]
    rfl
  let u := liftX (fun i => n.x i / 2)
  have huv : (2 : ℤ) • u.x = n.x := by
    funext i
    change 2 * (n.x i / 2) = n.x i
    have e := heven i
    omega
  have hb (a : V) : b a = bracket u.x a := by
    have hB := bracket_smul u.x a 2 1
    rw [one_smul, mul_one, huv, ← doubled] at hB
    funext i
    have e := congrFun hB i
    change 2 * b a i = 2 * bracket u.x a i at e
    omega
  let δ := MulAut.conj u⁻¹ * β
  have hδx (a : N) : (δ a).x = a.x := (conj_x u⁻¹ (β a)).trans (hx a)
  have hδz (a : N) : (δ a).z = a.z := by
    change (MulAut.conj u⁻¹ (β a)).z = _
    rw [conj_z, invN_x, hx, bz, hb]
    have hB := bracket_smul u.x a.x (-1) 1
    rw [neg_one_zsmul, one_smul, mul_one, neg_one_zsmul] at hB
    rw [hB, add_neg_cancel_right]
  obtain ⟨w, k, hk⟩ := pure_central δ hδx hδz
  refine ⟨u * liftZ w, 2 * k, ?_⟩
  have eq : β = MulAut.conj u * δ := by
    simp [δ, ← mul_assoc]
  rw [eq, hk, map_mul, mul_assoc]

private theorem normalizer (β γ : MulAut N) (n : N) (hγ : γ = α ∨ γ = α⁻¹)
    (h : ∀ a : N, β (α a) = MulAut.conj n (γ (β a))) :
    ∃ m : N, ∃ k : ℕ, β = MulAut.conj m * α ^ k := by
  have hx (a : N) : (β a).x = (β (central 1)).c • a.x :=
    (xMap_apply_N β a).trans ((automorphism_graded β).1 a.x)
  rcases central_sign β with hpos | hneg
  · exact normalizer_positive β γ n hγ (by simpa only [hpos, one_smul] using hx) h
  · let δ := β * α⁻¹
    have hδx (a : N) : (δ a).x = a.x := by
      change (β (α⁻¹ a)).x = _
      rw [hx, hneg, alpha_inv_x, neg_one_zsmul, neg_neg]
    have hδ (a : N) : δ (α a) = MulAut.conj n (γ (δ a)) := by
      change β (α.symm (α a)) = MulAut.conj n (γ (β (α.symm a)))
      rw [MulEquiv.symm_apply_apply]
      have he := h (α.symm a)
      rwa [MulEquiv.apply_symm_apply] at he
    obtain ⟨m, k, hk⟩ := normalizer_positive δ γ n hγ hδx hδ
    refine ⟨m, k + 1, ?_⟩
    rw [pow_succ, ← mul_assoc, ← hk]
    simp [δ, mul_assoc]

/-!
## The semidirect product

Every homomorphism to the infinite cyclic group kills the nilpotent subgroup. This makes the
subgroup characteristic. After removing the inner restriction, an automorphism can only translate
the cyclic generator by a central power, and an explicit conjugation supplies this translation.
-/

private def action : Multiplicative ℤ →* MulAut N where
  toFun k := α ^ k.toAdd
  map_one' := zpow_zero _
  map_mul' k l := zpow_add α k.toAdd l.toAdd

private abbrev G := N ⋊[action] Multiplicative ℤ
private abbrev embedN : N →* G := SemidirectProduct.inl
private abbrev proj : G →* Multiplicative ℤ := SemidirectProduct.rightHom

private def t : G := SemidirectProduct.inr (Multiplicative.ofAdd 1)

private theorem t_right : t.right = Multiplicative.ofAdd 1 := rfl

private theorem int_zpow (a k : ℤ) :
    (Multiplicative.ofAdd a) ^ k = Multiplicative.ofAdd (k * a) := rfl

private theorem decomp (g : G) : g = embedN g.left * t ^ g.right.toAdd := by
  rw [t, ← map_zpow, int_zpow, mul_one]
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

private theorem t_pow_conj (k : ℤ) (n : N) :
    MulAut.conj (t ^ k) (embedN n) = embedN ((α ^ k) n) := by
  rw [t, ← map_zpow, int_zpow, mul_one, MulAut.conj_apply]
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

private theorem t_pow_right (k : ℤ) : (t ^ k).right = Multiplicative.ofAdd k := by
  change proj (t ^ k) = _
  rw [map_zpow]
  change (Multiplicative.ofAdd 1) ^ k = _
  rw [int_zpow, mul_one]

private theorem kills_N (f : G →* Multiplicative ℤ) (n : N) : f (embedN n) = 1 := by
  have h := congrArg f (t_pow_conj 1 n)
  rw [zpow_one, zpow_one, MulAut.conj_apply, map_mul, map_mul, map_inv] at h
  have eq : f (embedN (α n)) = f (embedN n) := by
    rwa [mul_comm (f t), mul_assoc, mul_inv_cancel, mul_one, eq_comm] at h
  let g := f.comp embedN
  have ex := hom_factors_x g (α n)
  have ey := hom_factors_x g n⁻¹
  rw [alpha_x] at ex
  rw [invN_x] at ey
  have ez : g n = g n⁻¹ := eq.symm.trans (ex.trans ey.symm)
  rw [map_inv] at ez
  have ei := congrArg Multiplicative.toAdd ez
  change (g n).toAdd = -(g n).toAdd at ei
  change (g n).toAdd = 0
  omega

private theorem restrict_right (φ : MulAut G) (n : N) : (φ (embedN n)).right = 1 :=
  kills_N (proj.comp φ.toMonoidHom) n

private def restrictN (φ : MulAut G) : MulAut N where
  toFun n := (φ (embedN n)).left
  invFun n := (φ.symm (embedN n)).left
  left_inv n := by
    have h : embedN (φ (embedN n)).left = φ (embedN n) := by
      apply SemidirectProduct.ext
      · rfl
      · exact (restrict_right φ n).symm
    change (φ.symm (embedN (φ (embedN n)).left)).left = n
    rw [h, MulEquiv.symm_apply_apply]
    rfl
  right_inv n := by
    have h : embedN (φ.symm (embedN n)).left = φ.symm (embedN n) := by
      apply SemidirectProduct.ext
      · rfl
      · exact (restrict_right φ.symm n).symm
    change (φ (embedN (φ.symm (embedN n)).left)).left = n
    rw [h, MulEquiv.apply_symm_apply]
    rfl
  map_mul' n m := by
    rw [map_mul, map_mul, SemidirectProduct.mul_left, restrict_right, map_one]
    rfl

private theorem restrict_apply (φ : MulAut G) (n : N) :
    φ (embedN n) = embedN (restrictN φ n) := by
  apply SemidirectProduct.ext
  · rfl
  · exact restrict_right φ n

private theorem right_sign (φ : MulAut G) :
    (φ t).right.toAdd = 1 ∨ (φ t).right.toAdd = -1 := by
  obtain ⟨g, hg⟩ := φ.surjective t
  conv_lhs at hg => rw [decomp g, map_mul, map_zpow]
  have hr := congrArg proj hg
  rw [map_mul, map_zpow] at hr
  change (φ (embedN g.left)).right * (φ t).right ^ g.right.toAdd = t.right at hr
  rw [restrict_right, one_mul, t_right] at hr
  have hs := congrArg Multiplicative.toAdd hr
  change g.right.toAdd * (φ t).right.toAdd = 1 at hs
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa only [mul_comm] using hs)

private theorem restrict_normalizes (φ : MulAut G) (n : N) :
    restrictN φ (α n) =
      MulAut.conj (φ t).left ((α ^ (φ t).right.toAdd) (restrictN φ n)) := by
  have h := congrArg φ (t_pow_conj 1 n)
  rw [zpow_one, zpow_one] at h
  change φ (t * embedN n * t⁻¹) = _ at h
  rw [map_mul, map_mul, map_inv, restrict_apply φ n, restrict_apply φ (α n)] at h
  change MulAut.conj (φ t) (embedN (restrictN φ n)) = _ at h
  conv_lhs at h => rw [decomp (φ t), map_mul, MulAut.mul_apply, t_pow_conj]
  have hin (u v : N) : MulAut.conj (embedN u) (embedN v) = embedN (MulAut.conj u v) := by
    simp only [MulAut.conj_apply, map_mul, map_inv]
  rw [hin] at h
  exact (SemidirectProduct.inl_injective h).symm

private theorem restrict_inner_power (φ : MulAut G) :
    ∃ m : N, ∃ k : ℕ, restrictN φ = MulAut.conj m * α ^ k := by
  apply normalizer (restrictN φ) (α ^ (φ t).right.toAdd) (φ t).left
  · rcases right_sign φ with h | h
    · exact Or.inl (by rw [h, zpow_one])
    · exact Or.inr (by rw [h, zpow_neg_one])
  · exact restrict_normalizes φ

private theorem fixed_N_right (φ : MulAut G) (h : restrictN φ = 1) :
    (φ t).right.toAdd = 1 := by
  rcases right_sign φ with good | bad
  · exact good
  · exfalso
    apply alpha_sq_not_inner (φ t).left
    ext n : 1
    have he := restrict_normalizes φ (α n)
    simp only [h, MulAut.one_apply, bad, zpow_neg_one] at he
    change α (α n) = MulAut.conj (φ t).left (α.symm (α n)) at he
    rwa [MulEquiv.symm_apply_apply] at he

private theorem fixed_N_left (φ : MulAut G) (h : restrictN φ = 1) :
    ∃ j : ℤ, φ t = embedN (central j) * t := by
  have e := fixed_N_right φ h
  have hc : ∀ a, (φ t).left * a = a * (φ t).left := by
    intro a
    have he := restrict_normalizes φ (α.symm a)
    simp only [h, MulAut.one_apply, e, zpow_one, MulEquiv.apply_symm_apply] at he
    exact (commutatorElement_eq_one_iff_mul_comm.mp (by
      rwa [conj_eq_commutatorElement_mul, eq_comm, mul_eq_right] at he))
  obtain ⟨hx, hz⟩ := (center_N _).mp hc
  have hl : (φ t).left = central (φ t).left.c := by
    apply N.ext
    exacts [hx, hz, rfl]
  exact ⟨(φ t).left.c, by conv_lhs => rw [decomp (φ t), e, hl, zpow_one]⟩

private def s : G := embedN (liftZ qVector)⁻¹ * t ^ (4 : ℕ)

private theorem s_commute_N (n : N) : Commute s (embedN n) := by
  have h : MulAut.conj s (embedN n) = embedN n := by
    rw [s, map_mul, MulAut.mul_apply, ← zpow_natCast t 4, t_pow_conj, zpow_natCast, alpha_four]
    simp [MulAut.conj_apply, mul_assoc]
  exact (mul_inv_eq_iff_eq_mul).mp h

private theorem s_commute_t : s * t = embedN (central 1) * t * s := by
  apply SemidirectProduct.ext
  · have hleft : (t ^ (4 : ℕ)).left = 1 := by
      rw [t, ← map_pow]
      rfl
    have ht : t.left = 1 := rfl
    have htα : action t.right = α := zpow_one _
    simp only [s, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      one_mul, mul_one, map_one, ht, htα, hleft]
    rw [alpha_Rinv, mul_c, c_mul]
    simp
    rfl
  · change proj (s * t) = proj (embedN (central 1) * t * s)
    simp [mul_comm]

private theorem conj_s_pow_t (j : ℤ) :
    MulAut.conj (s ^ j) t = embedN (central j) * t := by
  let c := embedN (central 1)
  have h : MulAut.conj t s = c⁻¹ * s := by
    change t * s * t⁻¹ = _
    calc
      t * s * t⁻¹ = c⁻¹ * (c * t * s) * t⁻¹ := by simp [mul_assoc]
      _ = c⁻¹ * s := by rw [← s_commute_t]; simp [mul_assoc]
  have hp : c ^ j = embedN (central j) := by
    dsimp only [c]
    rw [← map_zpow]
    congr 1
    have he := centralHom.map_zpow (Multiplicative.ofAdd 1) j
    rw [int_zpow, mul_one] at he
    exact he.symm
  have e : t * s ^ j = (c ^ j)⁻¹ * s ^ j * t := by
    apply (mul_inv_eq_iff_eq_mul).mp
    change MulAut.conj t (s ^ j) = _
    rw [map_zpow, h, ((s_commute_N (central 1)).symm.inv_left).mul_zpow, inv_zpow]
  have e' : c ^ j * (t * s ^ j) = s ^ j * t := by
    rw [e]
    simp [mul_assoc]
  rw [MulAut.conj_apply, ← e', hp]
  simp [mul_assoc]

private theorem fixed_N_inner (φ : MulAut G) (h : restrictN φ = 1) :
    ∃ g : G, φ = MulAut.conj g := by
  obtain ⟨j, hj⟩ := fixed_N_left φ h
  have hn (n : N) : φ (embedN n) = MulAut.conj (s ^ j) (embedN n) := by
    rw [restrict_apply, h, MulAut.one_apply, MulAut.conj_apply]
    exact (mul_inv_eq_iff_eq_mul.mpr ((s_commute_N n).zpow_left j).eq).symm
  have ht : φ t = MulAut.conj (s ^ j) t := hj.trans (conj_s_pow_t j).symm
  refine ⟨s ^ j, ?_⟩
  ext g : 1
  rw [decomp g]
  simp only [map_mul, map_zpow, hn, ht]

private theorem all_inner (φ : MulAut G) : ∃ g : G, φ = MulAut.conj g := by
  obtain ⟨m, k, hk⟩ := restrict_inner_power φ
  let u := embedN m * t ^ k
  have hu (n : N) : MulAut.conj u (embedN n) = φ (embedN n) := by
    dsimp only [u]
    rw [map_mul, MulAut.mul_apply, ← zpow_natCast t k, t_pow_conj, zpow_natCast,
      restrict_apply φ n, hk, MulAut.mul_apply]
    simp only [MulAut.conj_apply, map_mul, map_inv]
  let ψ := (MulAut.conj u)⁻¹ * φ
  have hψ : restrictN ψ = 1 := by
    ext n : 1
    apply SemidirectProduct.inl_injective (φ := action)
    rw [← restrict_apply, MulAut.one_apply]
    change (MulAut.conj u).symm (φ (embedN n)) = _
    rw [← hu, MulEquiv.symm_apply_apply]
  obtain ⟨g, hg⟩ := fixed_N_inner ψ hψ
  refine ⟨u * g, ?_⟩
  rw [map_mul, ← hg]
  simp [ψ, ← mul_assoc]

/-!
## The normal series

Add the central coordinate first, followed by the five edge coordinates, the five vertex
coordinates, and the cyclic quotient. At each step the new coordinate induces the required
isomorphism of the factor with the additive integers.
-/

private def tailZero (k : ℕ) (a : V) : Prop := ∀ i : Fin 5, k ≤ i.val → a i = 0

private theorem tailZero_succ (i : Fin 5) (a : V) :
    tailZero (i.val + 1) a → (a i = 0 ↔ tailZero i.val a) := by
  intro h
  refine ⟨fun hi j hj => ?_, fun ha => ha i le_rfl⟩
  by_cases e : j = i
  · rwa [e]
  · apply h j
    have hne : j.val ≠ i.val := fun e' => e (Fin.ext e')
    omega

private theorem tailZero_node (i : Fin 5) (j : ℤ) : tailZero (i.val + 1) (j • node i) := by
  intro k hk
  have hne : k ≠ i := by
    rintro rfl
    omega
  simp [node, hne]

private def edgesBelow (k : ℕ) : Subgroup N where
  carrier := {n | n.x = 0 ∧ tailZero k n.z}
  one_mem' := ⟨rfl, fun _ _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    change a.x = 0 ∧ tailZero k a.z at ha
    change b.x = 0 ∧ tailZero k b.z at hb
    refine ⟨by simp [ha.1, hb.1], fun i hi => ?_⟩
    simp [ha.1, ha.2 i hi, hb.2 i hi]
  inv_mem' := by
    intro a ha
    change a.x = 0 ∧ tailZero k a.z at ha
    refine ⟨by simp [ha.1], fun i hi => ?_⟩
    simp [ha.1, ha.2 i hi]

private def verticesBelow (k : ℕ) : Subgroup N where
  carrier := {n | tailZero k n.x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  inv_mem' := fun ha i hi => by simp [ha i hi]

private theorem edgesBelow_normal (k : ℕ) : (edgesBelow k).Normal := by
  constructor
  intro a ha g
  change a.x = 0 ∧ tailZero k a.z at ha
  change (MulAut.conj g a).x = 0 ∧ tailZero k (MulAut.conj g a).z
  rw [conj_x, conj_z, ha.1, show bracket g.x 0 = 0 by simp [bracket], add_zero]
  exact ⟨rfl, ha.2⟩

private theorem verticesBelow_normal (k : ℕ) : (verticesBelow k).Normal := by
  constructor
  intro a ha g
  change tailZero k (MulAut.conj g a).x
  rwa [conj_x]

private theorem alpha_invariant_edges (k : ℕ) (n : N) :
    α n ∈ edgesBelow k ↔ n ∈ edgesBelow k := by
  change (-n.x = 0 ∧ tailZero k (n.z + twist n.x)) ↔ n.x = 0 ∧ tailZero k n.z
  simp only [neg_eq_zero]
  constructor <;> rintro ⟨hx, hz⟩ <;> exact ⟨hx, by simpa [hx] using hz⟩

private theorem alpha_invariant_vertices (k : ℕ) (n : N) :
    α n ∈ verticesBelow k ↔ n ∈ verticesBelow k := by
  change tailZero k (-n.x) ↔ tailZero k n.x
  simp [tailZero]

private theorem alpha_power_invariant (K : Subgroup N) (h : ∀ n, α n ∈ K ↔ n ∈ K)
    (j : ℤ) (n : N) : (α ^ j) n ∈ K ↔ n ∈ K := by
  have h_inv (a : N) : α.symm a ∈ K ↔ a ∈ K := by
    simpa only [MulEquiv.apply_symm_apply] using (h (α.symm a)).symm
  induction j using Int.induction_on generalizing n with
  | zero => simp
  | succ j ih =>
    rw [zpow_add, zpow_one, MulAut.mul_apply]
    exact (ih (α n)).trans (h n)
  | pred j ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, MulAut.mul_apply]
    exact (ih (α⁻¹ n)).trans (h_inv n)

private def liftSubgroup (K : Subgroup N) : Subgroup G := K.map embedN

private theorem lift_mem (K : Subgroup N) (g : G) :
    g ∈ liftSubgroup K ↔ g.left ∈ K ∧ g.right = 1 := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨hn, rfl⟩
  · rintro ⟨hl, hr⟩
    refine ⟨g.left, hl, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hr.symm

private theorem lift_normal (K : Subgroup N) (hN : K.Normal)
    (hA : ∀ n, α n ∈ K ↔ n ∈ K) : (liftSubgroup K).Normal := by
  constructor
  rintro g ⟨n, hn, rfl⟩ u
  change MulAut.conj u (embedN n) ∈ liftSubgroup K
  rw [decomp u, map_mul, MulAut.mul_apply, t_pow_conj]
  have h : (α ^ u.right.toAdd) n ∈ K :=
    (alpha_power_invariant K hA u.right.toAdd n).mpr hn
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  exact ⟨_, hN.conj_mem _ h _, rfl⟩

private abbrev E (i : ℕ) := liftSubgroup (edgesBelow i)
private abbrev V' (i : ℕ) := liftSubgroup (verticesBelow i)

private theorem E_normal (i : ℕ) : (E i).Normal :=
  lift_normal _ (edgesBelow_normal i) (alpha_invariant_edges i)

private theorem V_normal (i : ℕ) : (V' i).Normal :=
  lift_normal _ (verticesBelow_normal i) (alpha_invariant_vertices i)

private theorem E_five : E 5 = V' 0 := by
  ext g
  rw [lift_mem, lift_mem]
  have e : g.left ∈ edgesBelow 5 ↔ g.left ∈ verticesBelow 0 := by
    change (g.left.x = 0 ∧ tailZero 5 g.left.z) ↔ tailZero 0 g.left.x
    have hz : tailZero 5 g.left.z := fun i hi => False.elim (Nat.not_le_of_lt i.isLt hi)
    have hx : tailZero 0 g.left.x ↔ g.left.x = 0 := by
      constructor
      · intro h
        funext i
        exact h i (Nat.zero_le _)
      · intro h
        simp [h, tailZero]
    simp [hz, hx]
  rw [e]

private theorem V_five : V' 5 = proj.ker := by
  ext g
  rw [lift_mem, MonoidHom.mem_ker]
  change tailZero 5 g.left.x ∧ g.right = 1 ↔ g.right = 1
  exact and_iff_right (fun i hi => False.elim (Nat.not_le_of_lt i.isLt hi))

private def liftedLeft (K : Subgroup N) : liftSubgroup K →* N where
  toFun g := g.val.left
  map_one' := rfl
  map_mul' a b := by
    change (a.val * b.val).left = a.val.left * b.val.left
    simp [(lift_mem K a.val).mp a.property |>.2, SemidirectProduct.mul_left]

private def InfiniteCyclicFactor (L K : Subgroup G) : Prop :=
  L ≤ K ∧ ∃ _ : (L.subgroupOf K).Normal,
    IsCyclic (K ⧸ L.subgroupOf K) ∧ Infinite (K ⧸ L.subgroupOf K)

private theorem cyclic_factor {L K : Subgroup G} (h : L ≤ K) (f : K →* Multiplicative ℤ)
    (surj : Function.Surjective f) (ker : f.ker = L.subgroupOf K) : InfiniteCyclicFactor L K := by
  let : Infinite (Multiplicative ℤ) :=
    Infinite.of_injective (Multiplicative.ofAdd : ℤ → Multiplicative ℤ)
      Multiplicative.ofAdd.injective
  have e := QuotientGroup.quotientKerEquivOfSurjective f surj
  unfold InfiniteCyclicFactor
  refine ⟨h, ?_⟩
  rw [← ker]
  exact ⟨inferInstance, e.isCyclic.mpr inferInstance, Infinite.of_injective e.symm e.symm.injective⟩

private theorem bottom_factor :
    InfiniteCyclicFactor ⊥ (E 0) := by
  let f : E 0 →* Multiplicative ℤ :=
    { toFun := fun g => Multiplicative.ofAdd (g.val.left.c)
      map_one' := rfl
      map_mul' := fun a b => by
        change ((a.val * b.val).left).c = a.val.left.c + b.val.left.c
        have h := congrArg N.c ((liftedLeft (edgesBelow 0)).map_mul a b)
        change ((a.val * b.val).left).c = (a.val.left * b.val.left).c at h
        rw [h]
        have xzero : b.val.left.x = 0 := ((lift_mem _ _).mp b.property).1.1
        simp [xzero] }
  refine cyclic_factor bot_le f (fun a => ⟨⟨embedN (central a.toAdd), ?_⟩, rfl⟩) ?_
  · exact ⟨central a.toAdd, ⟨rfl, fun _ _ => rfl⟩, rfl⟩
  · ext g
    change (f g = 1) ↔ (g.val = 1)
    constructor
    · intro h
      have hc : g.val.left.c = 0 := congrArg Multiplicative.toAdd h
      obtain ⟨⟨hx, hz⟩, hr⟩ := (lift_mem _ _).mp g.property
      apply SemidirectProduct.ext
      · apply N.ext
        exacts [hx, funext (fun i => hz i (Nat.zero_le _)), hc]
      · exact hr
    · intro h
      change g.val.left.c = 0
      rw [h]
      rfl

private theorem edge_factor (i : Fin 5) :
    InfiniteCyclicFactor (E i.val) (E (i.val + 1)) := by
  let f : E (i.val + 1) →* Multiplicative ℤ :=
    { toFun := fun g => Multiplicative.ofAdd (g.val.left.z i)
      map_one' := rfl
      map_mul' := fun a b => by
        change ((a.val * b.val).left).z i = a.val.left.z i + b.val.left.z i
        have h := congrArg (fun x : N => x.z i) ((liftedLeft (edgesBelow _)).map_mul a b)
        change ((a.val * b.val).left).z i = (a.val.left * b.val.left).z i at h
        rw [h]
        have xzero : b.val.left.x = 0 := ((lift_mem _ _).mp b.property).1.1
        simp [xzero] }
  refine cyclic_factor ?_ f ?_ ?_
  · apply Subgroup.map_mono
    exact fun a ha => ⟨ha.1, fun j hj => ha.2 j (by omega)⟩
  · intro j
    refine ⟨⟨embedN (liftZ (j.toAdd • node i)), ⟨_, ⟨rfl, tailZero_node i _⟩, rfl⟩⟩, ?_⟩
    change (j.toAdd • node i) i = j.toAdd
    simp [node]
  · ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, lift_mem]
    obtain ⟨⟨hx, hz⟩, hr⟩ := (lift_mem _ _).mp g.property
    change g.val.left.z i = 0 ↔ (g.val.left.x = 0 ∧ tailZero i.val g.val.left.z) ∧ g.val.right = 1
    simp only [hx, hr, true_and, and_true]
    exact tailZero_succ i _ hz

private theorem vertex_factor (i : Fin 5) :
    InfiniteCyclicFactor (V' i.val) (V' (i.val + 1)) := by
  let f : V' (i.val + 1) →* Multiplicative ℤ :=
    { toFun := fun g => Multiplicative.ofAdd (g.val.left.x i)
      map_one' := rfl
      map_mul' := fun a b => by
        change ((a.val * b.val).left).x i = a.val.left.x i + b.val.left.x i
        have h := congrArg (fun x : N => x.x i) ((liftedLeft (verticesBelow _)).map_mul a b)
        exact h }
  refine cyclic_factor ?_ f ?_ ?_
  · apply Subgroup.map_mono
    exact fun a ha j hj => ha j (by omega)
  · intro j
    refine ⟨⟨embedN (liftX (j.toAdd • node i)), ⟨_, tailZero_node i _, rfl⟩⟩, ?_⟩
    change (j.toAdd • node i) i = j.toAdd
    simp [node]
  · ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, lift_mem]
    obtain ⟨hx, hr⟩ := (lift_mem _ _).mp g.property
    change g.val.left.x i = 0 ↔ tailZero i.val g.val.left.x ∧ g.val.right = 1
    simp only [hr, and_true]
    exact tailZero_succ i _ hx

private theorem top_factor :
    InfiniteCyclicFactor (V' 5) ⊤ := by
  apply cyclic_factor le_top (proj.domRestrict ⊤)
  · exact fun j => ⟨⟨SemidirectProduct.inr j, Subgroup.mem_top _⟩, rfl⟩
  · rw [MonoidHom.ker_domRestrict, V_five]

private def series : Fin 13 → Subgroup G :=
  ![⊥, E 0, E 1, E 2, E 3, E 4, E 5, V' 1, V' 2, V' 3, V' 4, V' 5, ⊤]

private theorem series_normal (j : Fin 13) : (series j).Normal := by
  fin_cases j
  exacts [inferInstanceAs (⊥ : Subgroup G).Normal, E_normal 0, E_normal 1, E_normal 2,
    E_normal 3, E_normal 4, E_normal 5, V_normal 1, V_normal 2, V_normal 3,
    V_normal 4, V_normal 5, inferInstanceAs (⊤ : Subgroup G).Normal]

private theorem series_factors (i : Fin 12) :
    InfiniteCyclicFactor (series i.castSucc) (series i.succ) := by
  fin_cases i
  · exact bottom_factor
  · exact edge_factor 0
  · exact edge_factor 1
  · exact edge_factor 2
  · exact edge_factor 3
  · exact edge_factor 4
  · change InfiniteCyclicFactor (E 5) (V' 1)
    rw [E_five]
    exact vertex_factor 0
  · exact vertex_factor 1
  · exact vertex_factor 2
  · exact vertex_factor 3
  · exact vertex_factor 4
  · exact top_factor

private theorem G_nontrivial : Nontrivial G := by
  refine ⟨⟨t, 1, fun h => ?_⟩⟩
  have e := congrArg (fun a : G => a.right.toAdd) h
  change (1 : ℤ) = 0 at e
  omega

@[expose] public section

/-- **Normal series with infinite cyclic factors.** A group $G$ has a normal series with infinite
cyclic factors when there are a natural number $n$ and subgroups
$1 = H_0 \le H_1 \le \cdots \le H_n = G$, each normal in $G$, such that every factor
$H_{i+1}/H_i$ is infinite cyclic. -/
def HasNormalSeriesInfiniteCyclicFactors (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    (∀ i, (H i).Normal) ∧ ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsCyclic (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ∧
          Infinite (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- **Outer automorphisms of groups with an infinite cyclic normal series (Kourovka 13.23).** The
conjecture that every nontrivial group with a normal series with infinite cyclic factors has an
automorphism that is not inner.

This is Kourovka Problem 13.23 (F. de Giovanni). -/
def polyInfiniteCyclicHasOuterAutomorphism : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G → HasNormalSeriesInfiniteCyclicFactors G →
    ∃ φ : MulAut G, ∀ g : G, φ ≠ MulAut.conj g

/--
**Only inner automorphisms despite an infinite cyclic normal series (Kourovka 13.23 refuted).**
There is a nontrivial group $G$ with a normal series with infinite cyclic factors such that every
automorphism of $G$ is inner. So the conjecture of Kourovka Problem 13.23 is false.

Brescia, Ingrosso and Trombetti construct a torsion-free group $G$ of Hirsch length $14$ with a
series $1 = G_0 \trianglelefteq \cdots \trianglelefteq G_{14} = G$ of normal subgroups of $G$
with infinite cyclic factors and $\mathrm{Out}(G) = 1$; the Kourovka Notebook (21st issue)
marks 13.23 solved, "No, not always".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 13.23 (F. de Giovanni); resolution: M.
Brescia, E. Ingrosso and M. Trombetti, A torsion-free supersoluble group with trivial outer
automorphism group, preprint (2026), arXiv:2607.11775, abstract: a torsion-free group of Hirsch
length 14 with a series 1 = G_0 ◁ ⋯ ◁ G_14 = G of normal subgroups of G with infinite cyclic
factors and Out(G) = 1; the Kourovka Notebook (21st issue) marks 13.23 solved,
https://arxiv.org/abs/2607.11775.
-/
theorem polyInfiniteCyclicHasOuterAutomorphism_refuted :
    ¬ polyInfiniteCyclicHasOuterAutomorphism := by
  intro conjecture
  have seriesG : HasNormalSeriesInfiniteCyclicFactors G :=
    ⟨12, series, rfl, rfl, series_normal, series_factors⟩
  obtain ⟨φ, hφ⟩ := conjecture G G_nontrivial seriesG
  obtain ⟨g, hg⟩ := all_inner φ
  exact hφ g hg

end

end MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23Wanted
