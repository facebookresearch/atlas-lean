/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.DeriveFintype

/-!
# Sylow 2-subgroups of rational groups (Kourovka Notebook Problem 16.36)

We refute the proposed inheritance of rationality by constructing a group of order 1536
with a Sylow subgroup of order 512 in which an element is not conjugate to its cube.

Write $V = Q_8/\{\pm1\}$. The normal subgroup is $(Q_8 \circ Q_8) \times V$, where the
central product identifies the two quaternion signs. The symmetric group on the three
imaginary axes acts on both quaternion factors and on $V$. A commuting involution adds
the first quaternion's image in $V$ to the vector coordinate. The preimage of the
stabilizer of the axis $i$ is a Sylow 2-subgroup. The product of $j$ in the first factor
with the commuting involution is the element that fails the conjugacy test there.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.36 (M. R.
Darafsheh). UnsolvedMath record UM-00701228 (`KOU-16.36`), dataset ulamai/UnsolvedMath v1.8.0.

Rationality is stated by the classical equivalent condition for finite groups: every `g` is
conjugate to every generator `g^k` (`k` coprime to the order of `g`) of `⟨g⟩`, since `χ(g)` is
rational iff it is fixed by the Galois automorphisms `ζ ↦ ζ^k` and characters separate conjugacy
classes. The Sylow subgroup is a group in its own right, so its conjugacy is internal.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36Wanted

/-- **Rational groups, conjugacy form.** A group $G$ is rational if every element $g \in G$ is
conjugate to $g^k$ for every natural number $k$ coprime to the order of $g$, where an element of
infinite order has order $0$, so that only $k = 1$ is coprime to it. For finite groups this is the
classical equivalent form of the condition that all ordinary characters of $G$ are
rational-valued. -/
def IsRationalGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, ∀ k : ℕ, Nat.Coprime k (orderOf g) → IsConj g (g ^ k)

/-- **Darafsheh's question on Sylow 2-subgroups of rational groups (Kourovka 16.36).** The
conjecture that for every finite rational group $G$, every Sylow $2$-subgroup of $G$, viewed as a
group in its own right, is rational. Here a group is rational if every element $g$ is conjugate
to $g^k$ for every natural number $k$ coprime to the order of $g$. -/
def sylowTwoOfRationalIsRational : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsRationalGroup G →
    ∀ P : Sylow 2 G, IsRationalGroup (P : Subgroup G)

/- The normal subgroup is the product of a four-group and the central product of two
quaternion groups (their central involutions are identified). Encode the axes of each
quaternion by the four-group, with 0, 1, 2, 3 representing 1, i, j, k modulo sign. -/
private abbrev Axis := BitVec 2
private instance axisFintype : Fintype Axis :=
  Fintype.ofEquiv (Fin 4) ⟨fun a => ⟨a⟩, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩

private abbrev Triangle := DihedralGroup 3

private def cycleAxis : Axis → Axis
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | _ => 0

private def reflectAxis : Axis → Axis
  | 2 => 3
  | 3 => 2
  | a => a

private def rotate (n : ZMod 3) (a : Axis) : Axis :=
  if n = 0 then a else if n = 1 then cycleAxis a else cycleAxis (cycleAxis a)

private def permute : Triangle → Axis → Axis
  | .r n, a => rotate n a
  | .sr n, a => reflectAxis (rotate n a)

-- An odd permutation of the quaternion axes changes the sign of each nontrivial axis.
private def permSign : Triangle → Axis → Bool
  | .r _, _ => false
  | .sr _, a => a != 0

-- Sign of the quaternion product of two unsigned axes.
private def mulSign (a b : Axis) : Bool :=
  a != 0 && b != 0 && (a == b || cycleAxis b == a)

-- Sign contributed by multiplying the first axis by the permuted second axis.
private def carry (p : Triangle) (a b : Axis) : Bool :=
  permSign p b ^^ mulSign a (permute p b)

private theorem permute_mul (p q : Triangle) (a : Axis) :
    permute (p * q) a = permute p (permute q a) := by decide +revert

private theorem permute_xor (p : Triangle) (a b : Axis) :
    permute p (a ^^^ b) = permute p a ^^^ permute p b := by decide +revert

private theorem carry_assoc (p q : Triangle) (a b c : Axis) :
    (carry p a b ^^ carry (p * q) (a ^^^ permute p b) c) =
      (carry q b c ^^ carry p a (b ^^^ permute q c)) := by decide +revert

/- The triangle group acts on all three copies of the four-group. A further involution
commutes with the triangle action and adds the first quaternion axis to the vector. -/
private structure Element where
  first : Axis
  second : Axis
  sign : Bool
  vector : Axis
  shear : Bool
  perm : Triangle
deriving DecidableEq, Fintype

private def scale (t : Bool) (a : Axis) : Axis := if t then a else 0

private def multiply (g h : Element) : Element where
  first := g.first ^^^ permute g.perm h.first
  second := g.second ^^^ permute g.perm h.second
  sign := g.sign ^^ h.sign ^^ carry g.perm g.first h.first ^^ carry g.perm g.second h.second
  vector := g.vector ^^^ permute g.perm h.vector ^^^ scale g.shear (permute g.perm h.first)
  shear := g.shear ^^ h.shear
  perm := g.perm * h.perm

private def identity : Element := ⟨0, 0, false, 0, false, 1⟩

private def inverse (g : Element) : Element :=
  let p := g.perm⁻¹
  let a := permute p g.first
  let b := permute p g.second
  ⟨a, b, g.sign ^^ carry p a g.first ^^ carry p b g.second,
    permute p g.vector ^^^ scale g.shear a, g.shear, p⟩

private instance elementMul : Mul Element := ⟨multiply⟩
private instance elementOne : One Element := ⟨identity⟩
private instance elementInv : Inv Element := ⟨inverse⟩

private theorem vector_assoc (p q : Triangle) (t s : Bool) (a b : Axis) :
    scale (t ^^ s) (permute (p * q) b) ^^^ scale t (permute p a) =
      permute p (scale s (permute q b)) ^^^ scale t (permute p (a ^^^ permute q b)) := by
  decide +revert

private instance elementGroup : Group Element := Group.ofLeftAxioms
  (by
    intro g h j
    change multiply (multiply g h) j = multiply g (multiply h j)
    simp only [multiply, Element.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, Bool.xor_assoc .., mul_assoc ..⟩
    · rw [permute_xor, permute_mul, BitVec.xor_assoc]
    · rw [permute_xor, permute_mul, BitVec.xor_assoc]
    · have h₁ := carry_assoc g.perm h.perm g.first h.first j.first
      have h₂ := carry_assoc g.perm h.perm g.second h.second j.second
      have h := congrArg₂ (fun a b => (g.sign ^^ h.sign ^^ j.sign) ^^ a ^^ b) h₁ h₂
      convert h using 1 <;> simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
    · have hv := vector_assoc g.perm h.perm g.shear h.shear h.first j.first
      simp only [permute_xor, permute_mul] at hv ⊢
      have h := congrArg (fun a => g.vector ^^^ permute g.perm h.vector ^^^
        permute g.perm (permute h.perm j.vector) ^^^ a) hv
      convert h using 1 <;> ac_rfl)
  (by rintro ⟨a, b, z, x, t, p⟩; decide +revert +kernel)
  (by rintro ⟨a, b, z, x, t, p⟩; decide +revert +kernel)

-- Search for a conjugator one coordinate at a time. The sign is central and can be set
-- to zero. The equations in the triangle and the two axes discard impossible prefixes.
private def hasConjugator (g h : Element) : Prop :=
  ∃ p : Triangle, p * g.perm = h.perm * p ∧
    ∃ a : Axis, a ^^^ permute p g.first = h.first ^^^ permute h.perm a ∧
      ∃ b : Axis, b ^^^ permute p g.second = h.second ^^^ permute h.perm b ∧
        (g.sign ^^ carry p a g.first ^^ carry p b g.second) =
          (h.sign ^^ carry h.perm h.first a ^^ carry h.perm h.second b) ∧
        ∃ t : Bool, ∃ x : Axis,
          let c : Element := ⟨a, b, false, x, t, p⟩
          c * g = h * c

private instance conjugatorDecidable (g h : Element) : Decidable (hasConjugator g h) := by
  unfold hasConjugator
  infer_instance

private theorem conj_of_search {g h : Element} (hc : hasConjugator g h) : IsConj g h := by
  obtain ⟨p, _, a, _, b, _, _, t, x, he⟩ := hc
  exact isConj_iff.mpr ⟨⟨a, b, false, x, t, p⟩, mul_inv_eq_iff_eq_mul.mpr he⟩

private def period (g : Element) : ℕ :=
  if g = 1 then 1 else if g ^ 2 = 1 then 2 else if g ^ 3 = 1 then 3
  else if g ^ 4 = 1 then 4 else if g ^ 6 = 1 then 6 else 8

private theorem period_spec (g : Element) :
    0 < period g ∧ g ^ period g = 1 ∧ ∀ i : Fin (period g), 0 < i.val → g ^ i.val ≠ 1 := by
  obtain ⟨a, b, z, x, t, p⟩ := g
  decide +revert +kernel

private theorem axis_cases (a : Axis) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide +revert

set_option maxHeartbeats 800000 in
-- Check the coprime powers of all 1536 elements, in batches indexed by the two axes.
private theorem coprime_powers (g : Element) :
    ∀ i : Fin (period g), i.val.Coprime (period g) → g ≠ g ^ i.val →
      hasConjugator g (g ^ i.val) := by
  obtain ⟨a, b, z, x, t, p⟩ := g
  rcases axis_cases a with rfl | rfl | rfl | rfl <;>
    rcases axis_cases b with rfl | rfl | rfl | rfl <;> decide +revert +kernel

private theorem rational : IsRationalGroup Element := by
  intro g k hk
  obtain ⟨hn, he, hm⟩ := period_spec g
  have ho : orderOf g = period g :=
    (orderOf_eq_iff hn).mpr ⟨he, fun i hi => hm ⟨i, hi⟩⟩
  rw [← pow_mod_orderOf, ho]
  by_cases h : g = g ^ (k % period g)
  · rw [← h]
  apply conj_of_search (coprime_powers g ⟨k % period g, Nat.mod_lt _ hn⟩ _ h)
  rw [ho] at hk
  exact (ZMod.coprime_mod_iff_coprime ..).mpr hk

private def stabilizer : Subgroup Element where
  carrier := {g | permute g.perm 1 = 1}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change permute (g.perm * h.perm) 1 = 1
    rw [permute_mul, show permute h.perm 1 = 1 from hh]
    exact hg
  inv_mem' {g} hg := by
    change permute g.perm⁻¹ 1 = 1
    calc
      _ = permute g.perm⁻¹ (permute g.perm 1) := congrArg _ hg.symm
      _ = 1 := by rw [← permute_mul, inv_mul_cancel]; rfl

private theorem card_element : Nat.card Element = 1536 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem card_stabilizer : Nat.card stabilizer = 512 := by
  change Nat.card {g : Element // permute g.perm 1 = 1} = 512
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def sylow : Sylow 2 Element :=
  (IsPGroup.of_card (show Nat.card stabilizer = 2 ^ 9 from card_stabilizer)).toSylow (by
    have hi := stabilizer.card_mul_index
    rw [card_element, card_stabilizer] at hi
    omega)

-- Take the second imaginary axis in the first quaternion factor, times the shear.
private def witness : stabilizer := ⟨⟨2, 0, false, 0, true, 1⟩, rfl⟩

private theorem not_rational : ¬ IsRationalGroup stabilizer := by
  intro h
  have ho : orderOf witness ∣ 4 := orderOf_dvd_of_pow_eq_one (by decide)
  have hc := h witness 3 ((show Nat.Coprime 3 4 by decide).of_dvd_right ho)
  obtain ⟨c, he⟩ := isConj_iff.mp hc
  have he' := congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp he)
  have impossible (g : Element) : permute g.perm 1 = 1 →
      g * witness.val ≠ witness.val ^ 3 * g := by
    obtain ⟨a, b, z, x, t, p⟩ := g
    decide +revert +kernel
  exact impossible c.val c.property he'

/--
**Sylow 2-subgroups of rational groups need not be rational (Kourovka 16.36).** There is a
finite rational group with a Sylow $2$-subgroup that is not rational as a group in its own right.
Here a group is rational if every element $g$ is conjugate to $g^k$ for every natural number $k$
coprime to the order of $g$.

The Kourovka Archive answers 16.36 "No, not always", citing Isaacs and Navarro (2012).

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.36 (M. R. Darafsheh);
resolution: I. M. Isaacs and G. Navarro, Math. Z. 272 (2012), 937-945, Kourovka Archive, Problem
16.36 (No, not always).
-/
public theorem sylowTwoOfRationalIsRational_refuted : ¬ sylowTwoOfRationalIsRational := by
  intro h
  exact not_rational (h Element rational sylow)

end MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36Wanted
