/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Groups all of whose automorphisms preserve conjugacy classes

The restricted direct product of the affine groups over the odd prime fields refutes the claim
of Kourovka Problem 16.62. Every automorphism acts by conjugation on each coordinate, but a
simultaneous dilation in infinitely many coordinates induces an outer automorphism.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.62 (D.
MacHale). UnsolvedMath record UM-00701254 (`KOU-16.62`), dataset ulamai/UnsolvedMath v1.8.0.

`α` fixes every conjugacy class setwise exactly when `α(g)` is conjugate to `g` for every `g`. The
hypothesis concerns all automorphisms of `G` at once, so this refutation is stronger than that of
`ScottishBook112Wanted` (every class-preserving automorphism is inner).
-/

namespace MathlibExt.GroupTheory.ClassPreservingAutomorphismsInnerKourovka16Problem62Wanted

noncomputable section

open Filter
open scoped RestrictedProduct

private abbrev prime (i : ℕ) := Nat.nth Nat.Prime (i + 1)

private instance primeFact (i : ℕ) : Fact (prime i).Prime :=
  ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _⟩

private theorem two_lt_prime (i : ℕ) : 2 < prime i := by
  simpa [prime] using Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.zero_lt_succ i)

private abbrev K (i : ℕ) := ZMod (prime i)

private theorem two_ne_zero (i : ℕ) : (2 : K i) ≠ 0 := by
  exact fun h => (Nat.not_dvd_of_pos_of_lt (by decide) (two_lt_prime i))
    ((ZMod.natCast_eq_zero_iff 2 _).mp h)

private abbrev Aff (i : ℕ) :=
  Multiplicative (K i) ⋊[(MulAutMultiplicative (K i)).symm.toMonoidHom.comp AddAut.mulLeft] (K i)ˣ

private abbrev offset {i : ℕ} (x : Aff i) : K i := x.left.toAdd

private abbrev slope {i : ℕ} (x : Aff i) : K i := x.right.val

private theorem affine_ext {i : ℕ} {x y : Aff i} (hb : offset x = offset y)
    (ha : slope x = slope y) : x = y :=
  SemidirectProduct.ext hb (Units.ext ha)

private abbrev trivialAt (i : ℕ) : Subgroup (Aff i) := ⊥

private abbrev G := Πʳ i, [Aff i, trivialAt i]

private abbrev single (i : ℕ) := RestrictedProduct.mulSingleMonoidHom trivialAt i

private abbrev tr {i : ℕ} (u : K i) : Aff i := SemidirectProduct.inl (.ofAdd u)

private abbrev shift (i : ℕ) (u : K i) : G := single i (tr u)

private abbrev dilation (i : ℕ) : Aff i :=
  SemidirectProduct.inr (Units.mk0 (2 : K i) (two_ne_zero i))

private abbrev doubleAt (i : ℕ) : G := single i (dilation i)

private theorem slope_doubleAt (i : ℕ) : slope (doubleAt i i) = 2 := by
  rw [doubleAt, single, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.mulSingle_eq_same]
  rfl

private theorem tr_pow {i : ℕ} (u : K i) (n : ℕ) : tr u ^ n = tr ((n : K i) * u) := by
  rw [tr, ← map_pow]
  exact congrArg SemidirectProduct.inl (show n • u = n * u from nsmul_eq_mul ..)

private theorem shift_pow (i : ℕ) (u : K i) (n : ℕ) : shift i u ^ n = shift i (n * u) := by
  rw [shift, ← map_pow, tr_pow]

private theorem map_shift {H : Type*} [Group H] (f : G →* H) (i : ℕ) (u : K i) :
    f (shift i u) = f (shift i 1) ^ u.val := by
  rw [← map_pow, shift_pow, ZMod.natCast_zmod_val, mul_one]

-- Conjugation by an affine map multiplies a translation by its slope.
private theorem mul_shift (x : G) (i : ℕ) (u : K i) :
    x * shift i u = shift i (slope (x i) * u) * x := by
  apply RestrictedProduct.ext
  intro j
  rcases eq_or_ne j i with rfl | h
  · simp only [RestrictedProduct.mul_apply, shift, single,
      RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.mulSingle_eq_same]
    apply affine_ext
    · change offset (x j) + slope (x j) * u = slope (x j) * u + 1 * offset (x j)
      ring
    · change slope (x j) * 1 = 1 * slope (x j)
      simp
  · simp [shift, single, h]

-- The commutator with doubling recovers the offset at the same coordinate.
private theorem mul_doubleAt (x : G) (i : ℕ) :
    x * doubleAt i = shift i (-offset (x i)) * doubleAt i * x := by
  apply RestrictedProduct.ext
  intro j
  rcases eq_or_ne j i with rfl | h
  · simp only [RestrictedProduct.mul_apply, shift, doubleAt, single,
      RestrictedProduct.mulSingleMonoidHom_apply, RestrictedProduct.mulSingle_eq_same]
    apply affine_ext
    · change offset (x j) + slope (x j) * 0 = -offset (x j) + 1 * 0 + 1 * 2 * offset (x j)
      ring
    · change slope (x j) * 2 = 1 * 2 * slope (x j)
      ring
  · simp [shift, doubleAt, single, h]

private abbrev project (f : MulAut G) (j : ℕ) : G →* Aff j :=
  (RestrictedProduct.evalMonoidHom Aff j).comp f.toMonoidHom

-- Doubling conjugates a unit translation to its square. Its image therefore has trivial slope.
private theorem image_shift_slope (f : MulAut G) (i j : ℕ) :
    slope (project f j (shift i 1)) = 1 := by
  have h := mul_shift (doubleAt i) i 1
  rw [slope_doubleAt, mul_one] at h
  have hsq : shift i (2 : K i) = shift i 1 ^ 2 := by
    rw [shift_pow]
    simp
  rw [hsq] at h
  have he := congrArg (fun g => (project f j g).right) h
  simp only [map_mul, map_pow, SemidirectProduct.mul_right] at he
  change _ = ((project f j (shift i 1)) ^ 2).right * _ at he
  rw [pow_two, SemidirectProduct.mul_right, mul_comm] at he
  exact congrArg Units.val (mul_eq_left.mp (mul_right_cancel he).symm)

private theorem image_shift_tr (f : MulAut G) (i j : ℕ) :
    project f j (shift i 1) = tr (offset (project f j (shift i 1))) :=
  affine_ext rfl (image_shift_slope f i j)

-- A translation of order p has trivial image in the translation group at every other prime.
private theorem image_shift_other (f : MulAut G) {i j : ℕ} (hij : i ≠ j) :
    project f j (shift i 1) = 1 := by
  have hpow : shift i 1 ^ prime i = 1 := by
    rw [shift_pow, ZMod.natCast_self, zero_mul]
    exact map_one (single i)
  have h := congrArg (project f j) hpow
  rw [map_pow, map_one, image_shift_tr f i j, tr_pow] at h
  have hz : (prime i : K j) * offset (project f j (shift i 1)) = 0 :=
    congrArg offset h
  have hn : (prime i : K j) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp he
    have hp := ((primeFact i).out.dvd_iff_eq (primeFact j).out.ne_one).mp hd
    exact hij (Nat.succ.inj (Nat.nth_injective Nat.infinite_setOfPred_prime hp))
  exact affine_ext ((mul_eq_zero.mp hz).resolve_left hn) (image_shift_slope ..)

private abbrev coeff (f : MulAut G) (i : ℕ) := offset (project f i (shift i 1))

private theorem coeff_ne_zero (f : MulAut G) (i : ℕ) : coeff f i ≠ 0 := by
  intro hz
  have h : f (shift i 1) = 1 := by
    apply RestrictedProduct.ext
    intro j
    rcases eq_or_ne i j with rfl | hij
    · exact affine_ext hz (image_shift_slope f i i)
    · exact image_shift_other f hij
  have he := (map_eq_one_iff f f.injective).mp h
  have ht := congrArg (fun x : G => x i) he
  simp only [shift, single, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.mulSingle_eq_same, RestrictedProduct.one_apply] at ht
  exact one_ne_zero (congrArg offset ht : (1 : K i) = 0)

private theorem image_shift_same (f : MulAut G) (i : ℕ) (u : K i) :
    project f i (shift i u) = tr (u * coeff f i) := by
  calc
    _ = project f i (shift i 1) ^ u.val := map_shift ..
    _ = tr (coeff f i) ^ u.val := congrArg (· ^ u.val) (image_shift_tr ..)
    _ = _ := by rw [tr_pow, ZMod.natCast_zmod_val]

private theorem slope_preserved (f : MulAut G) (x : G) (i : ℕ) :
    slope (f x i) = slope (x i) := by
  have h := congrArg (project f i) (mul_shift x i 1)
  rw [mul_one, map_mul, map_mul, image_shift_same, image_shift_same, one_mul] at h
  have ht := congrArg offset h
  change offset (f x i) + slope (f x i) * coeff f i =
    slope (x i) * coeff f i + 1 * offset (f x i) at ht
  rw [one_mul, add_comm (offset (f x i)), add_left_inj] at ht
  exact mul_right_cancel₀ (coeff_ne_zero f i) ht

-- After applying f, the images of the unit translation and the dilation determine a
-- single affine change of coordinates: its slope is coeff f i and its offset is -v.
private theorem local_conjugator (f : MulAut G) (i : ℕ) :
    ∃ k : Aff i, ∀ x : G, k * x i = f x i * k := by
  let v := offset (f (doubleAt i) i)
  let k : Aff i := ⟨.ofAdd (-v), Units.mk0 (coeff f i) (coeff_ne_zero f i)⟩
  have hd : slope (f (doubleAt i) i) = 2 := by
    rw [slope_preserved, slope_doubleAt]
  refine ⟨k, fun x => affine_ext ?_ ?_⟩
  · have h := congrArg (project f i) (mul_doubleAt x i)
    simp only [map_mul, image_shift_same] at h
    have ht := congrArg offset h
    change offset (f x i) + slope (f x i) * v =
      -offset (x i) * coeff f i + 1 * v + (1 * slope (f (doubleAt i) i)) * offset (f x i) at ht
    rw [hd] at ht
    change -v + coeff f i * offset (x i) = offset (f x i) + slope (f x i) * -v
    linear_combination ht
  · change coeff f i * slope (x i) = slope (f x i) * coeff f i
    rw [slope_preserved, mul_comm]

private theorem all_class_preserving (f : MulAut G) (x : G) : IsConj (f x) x := by
  classical
  choose k hk using local_conjugator f
  -- Only coordinates in the support of x need a conjugator.
  let c : G := ⟨fun i => if x i = 1 then 1 else k i, by
    filter_upwards [x.eventually] with i hi
    simp_all [trivialAt]⟩
  apply IsConj.symm
  refine isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply RestrictedProduct.ext
  intro i
  change (if x i = 1 then 1 else k i) * x i = f x i * (if x i = 1 then 1 else k i)
  by_cases hi : x i = 1
  · have he : f x i * k i = 1 * k i := by simpa [hi] using (hk i x).symm
    simp [hi, mul_right_cancel he]
  · simpa [hi] using hk i x

-- Conjugating in every factor by a doubling map preserves finite support.
private def coordMap (e : ∀ i, MulAut (Aff i)) (x : G) : G :=
  ⟨fun i => e i (x i), by
    filter_upwards [x.eventually] with i hi
    change e i (x i) = 1
    rw [show x i = 1 from hi, map_one]⟩

private def simultaneousDoubling : MulAut G where
  toFun := coordMap fun i => MulAut.conj (dilation i)
  invFun := coordMap fun i => (MulAut.conj (dilation i)).symm
  left_inv x :=
    RestrictedProduct.ext Aff _ fun i => (MulAut.conj (dilation i)).symm_apply_apply (x i)
  right_inv x :=
    RestrictedProduct.ext Aff _ fun i => (MulAut.conj (dilation i)).apply_symm_apply (x i)
  map_mul' x y :=
    RestrictedProduct.ext Aff _ fun i => map_mul (MulAut.conj (dilation i)) (x i) (y i)

private theorem doubling_outer (h : G) : simultaneousDoubling ≠ MulAut.conj h := by
  intro he
  obtain ⟨i, hi⟩ := h.eventually.exists
  have hi' : h i = 1 := hi
  have ht := congrArg (fun f : MulAut G => f (shift i 1) i) he
  change MulAut.conj (dilation i) (shift i 1 i) = h i * shift i 1 i * (h i)⁻¹ at ht
  rw [hi', one_mul, inv_one, mul_one, shift, single, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.mulSingle_eq_same, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at ht
  have hb := congrArg offset ht
  change (0 : K i) + 2 * 1 = 1 + 1 * 0 at hb
  have hn : (1 : K i) = 0 := by linear_combination hb
  exact one_ne_zero hn

end

@[expose] public section

/-- **Claim of Kourovka Problem 16.62.** For every group $G$: if every automorphism of $G$ sends
each element $g \in G$ to a conjugate of $g$ (equivalently, maps every conjugacy class of $G$ into
itself), then every automorphism of $G$ is inner, that is, of the form $x \mapsto h x h^{-1}$ for
some $h \in G$. -/
def classPreservingAutomorphismsInner : Prop :=
  ∀ (G : Type) [Group G], (∀ (α : MulAut G) (g : G), IsConj (α g) g) →
    ∀ α : MulAut G, ∃ h : G, α = MulAut.conj h

/--
**Groups whose automorphisms all preserve conjugacy classes can have outer automorphisms.** The
claim of Kourovka Problem 16.62 is false: there is a group $G$ such that every automorphism of $G$
sends each element $g \in G$ to a conjugate of $g$, but some automorphism of $G$ is not inner,
that is, not of the form $x \mapsto h x h^{-1}$ for any $h \in G$.

Heineken constructed finite $p$-groups all of whose automorphisms preserve every conjugacy class,
and Gaschütz' theorem gives these groups outer automorphisms.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.62 (D.
MacHale); resolution: H. Heineken, Arch. Math. (Basel) 33 (1979/80), no. 6, 497-503; A. Mann,
letter of 20 April 2006, as recorded in the Kourovka Archive, Kourovka Archive, Problem 16.62 (Not
necessarily: Heineken's finite p-groups all of whose automorphisms preserve all conjugacy classes
have outer automorphisms by Gaschütz' theorem).
-/
theorem classPreservingAutomorphismsInner_refuted :
    ¬ classPreservingAutomorphismsInner := by
  intro claim
  obtain ⟨h, he⟩ := claim G all_class_preserving simultaneousDoubling
  exact doubling_outer h he

end

end MathlibExt.GroupTheory.ClassPreservingAutomorphismsInnerKourovka16Problem62Wanted
