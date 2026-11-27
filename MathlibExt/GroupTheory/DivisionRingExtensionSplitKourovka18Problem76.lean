/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Extensions of the additive group of a division ring (Kourovka Notebook Problem 18.76)

This module proves that a division ring with two commuting copies of a rank-two free group
in its units admits a nonsplit extension with the given action. It constructs such a division
ring by Ore localization of a skew polynomial ring.

Kourovka Notebook, Problem 18.76 (E. A. Palyutin), marked solved in the 21st issue: let `A` be a
division ring, `G` a subgroup of the multiplicative group of `A`, and `E` an extension of the
additive group of `A` by `G` such that `G` acts by multiplication in `A`. Is it true that `E`
splits? This is true if `G` is finite.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.76 (E. A. Palyutin). UnsolvedMath record
UM-00701505 (`KOU-18.76`), dataset ulamai/UnsolvedMath v1.8.0.

The extension is an injective `i : Multiplicative A →* E` and a surjective `π : E →* G` with `range
i = ker π` and `e · i(a) · e⁻¹ = i(π(e) a)` (left multiplication, the action in the resolving
construction); it splits when `π` has a homomorphic section. The resolution is by AI-generated
solutions confirmed by B. A. F. Wehrfritz.
-/

namespace MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76Wanted

@[expose] public section

/-- **Palyutin's splitting problem for division rings (Kourovka 18.76).** The statement that for
every division ring $A$, every subgroup $G$ of its unit group $A^\times$ and every group $E$, if
$i$ is an injective homomorphism from the additive group of $A$ to $E$ and $\pi : E \to G$ is a
surjective homomorphism whose kernel is the image of $i$, such that
$e \, i(a) \, e^{-1} = i(\pi(e) a)$ for all $e \in E$ and $a \in A$ (so $G$ acts on the kernel by
left multiplication), then the extension splits: there is a homomorphism $s : G \to E$ with
$\pi(s(g)) = g$ for every $g \in G$. -/
def divisionRingMultiplicationExtensionsSplit : Prop :=
  ∀ (A : Type) [DivisionRing A] (G : Subgroup Aˣ) (E : Type) [Group E]
    (i : Multiplicative A →* E) (π : E →* G), Function.Injective i → Function.Surjective π →
    i.range = π.ker →
    (∀ (e : E) (a : A), e * i (Multiplicative.ofAdd a) * e⁻¹ =
      i (Multiplicative.ofAdd (((π e : Aˣ) : A) * a))) →
    ∃ s : G →* E, ∀ g : G, π (s g) = g

end

/-! ## The nonsplit extension

A shear on the first semidirect product assigns a single nonzero
defect to the pair of second generators. A section would make all four pairs of lifts commute.
-/

section Extension

open Multiplicative

private abbrev F := FreeGroup Bool

variable {A : Type} [DivisionRing A]

private def scalars : Aˣ →* MulAut (Multiplicative A) where
  toFun u :=
    { toFun := fun x => ofAdd ((u : A) * x.toAdd)
      invFun := fun x => ofAdd ((↑u⁻¹ : A) * x.toAdd)
      left_inv := fun x => by
        apply toAdd.injective
        change (↑u⁻¹ : A) * ((u : A) * x.toAdd) = x.toAdd
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun x => by
        apply toAdd.injective
        change (u : A) * ((↑u⁻¹ : A) * x.toAdd) = x.toAdd
        rw [← mul_assoc, Units.mul_inv, one_mul]
      map_mul' := fun x y => by
        apply toAdd.injective
        exact mul_add (u : A) x.toAdd y.toAdd }
  map_one' := by ext x; exact congrArg ofAdd (one_mul (toAdd x))
  map_mul' u v := by ext x; exact congrArg ofAdd (mul_assoc (u : A) (v : A) (toAdd x))

private abbrev N (a : F →* Aˣ) := Multiplicative A ⋊[scalars.comp a] F

private def shift (a : F →* Aˣ) (c : Bool → A) : F →* N a :=
  FreeGroup.lift fun i => ⟨ofAdd (c i), FreeGroup.of i⟩

private theorem shift_right (a : F →* Aˣ) (c : Bool → A) (f : F) :
    (shift a c f).right = f := by
  have h : SemidirectProduct.rightHom.comp (shift a c) = MonoidHom.id F := by
    ext i
    simp [shift]
  exact DFunLike.congr_fun h f

private def defect (a : F →* Aˣ) (c : Bool → A) (f : F) : A :=
  (shift a c f).left.toAdd

private theorem defect_of (a : F →* Aˣ) (c : Bool → A) (i : Bool) :
    defect a c (FreeGroup.of i) = c i := by
  simp [defect, shift]

private theorem defect_one (a : F →* Aˣ) (c : Bool → A) : defect a c 1 = 0 := by
  simp [defect]

private theorem defect_mul (a : F →* Aˣ) (c : Bool → A) (f g : F) :
    defect a c (f * g) = defect a c f + (a f : A) * defect a c g := by
  simp only [defect, map_mul, SemidirectProduct.mul_left, shift_right]
  rfl

private def shear (a : F →* Aˣ) (b : Aˣ) (hb : ∀ f, Commute b (a f)) (c : Bool → A) :
    MulAut (N a) where
  toFun x := ⟨ofAdd ((b : A) * x.left.toAdd + defect a c x.right), x.right⟩
  invFun x := ⟨ofAdd ((↑b⁻¹ : A) * (x.left.toAdd - defect a c x.right)), x.right⟩
  left_inv x := by
    refine SemidirectProduct.ext ?_ rfl
    apply toAdd.injective
    change (↑b⁻¹ : A) * ((b : A) * x.left.toAdd + _ - _) = x.left.toAdd
    rw [add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    refine SemidirectProduct.ext ?_ rfl
    apply toAdd.injective
    change (b : A) * ((↑b⁻¹ : A) * (x.left.toAdd - _)) + _ = x.left.toAdd
    rw [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]
  map_mul' x y := by
    refine SemidirectProduct.ext ?_ rfl
    apply toAdd.injective
    change (b : A) * (x.left.toAdd + (a x.right : A) * y.left.toAdd) +
        defect a c (x.right * y.right) =
      ((b : A) * x.left.toAdd + defect a c x.right) +
        (a x.right : A) * ((b : A) * y.left.toAdd + defect a c y.right)
    have h : (b : A) * (a x.right : A) = (a x.right : A) * (b : A) :=
      congrArg Units.val (hb x.right).eq
    rw [defect_mul, mul_add, mul_add, ← mul_assoc (b : A), h, mul_assoc]
    ac_rfl

private def twists (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) : F →* MulAut (N a) :=
  FreeGroup.lift fun j =>
    shear a (b (FreeGroup.of j)) (fun f => (h f (FreeGroup.of j)).symm)
      fun i => if i && j then 1 else 0

private theorem twists_apply_of (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g))
    (j : Bool) (x : N a) :
    twists a b h (FreeGroup.of j) x =
      ⟨ofAdd ((b (FreeGroup.of j) : A) * x.left.toAdd +
        defect a (fun i => if i && j then 1 else 0) x.right), x.right⟩ := by
  rw [twists, FreeGroup.lift_apply_of]
  rfl

private abbrev E (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) :=
  N a ⋊[twists a b h] F

private theorem twists_properties (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g))
    (g : F) : (∀ x : N a, (twists a b h g x).right = x.right) ∧
      ∀ z : A, twists a b h g ⟨ofAdd z, 1⟩ = ⟨ofAdd ((b g : A) * z), 1⟩ := by
  induction g using FreeGroup.induction_on with
  | one => simp
  | of j =>
    constructor
    · intro x
      rw [twists_apply_of]
    · intro z
      rw [twists_apply_of, defect_one, add_zero]
      rfl
  | inv_of j ih =>
    let g := FreeGroup.of j
    constructor
    · intro x
      change (twists a b h g⁻¹ x).right = x.right
      have he := ih.1 (twists a b h g⁻¹ x)
      rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, eq_comm]
        at he
    · intro z
      change twists a b h g⁻¹ ⟨ofAdd z, 1⟩ = ⟨ofAdd ((b g⁻¹ : A) * z), 1⟩
      apply (twists a b h g).injective
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, ih.2]
      have he : (b (FreeGroup.of j) : A) * (b g⁻¹ : A) * z = z := by
        change (b g : A) * (b g⁻¹ : A) * z = z
        rw [map_inv, Units.mul_inv, one_mul]
      rw [← mul_assoc, he]
  | mul f g hf hg =>
    constructor
    · intro x
      rw [map_mul, MulAut.mul_apply, hf.1, hg.1]
    · intro z
      rw [map_mul, MulAut.mul_apply, hg.2, hf.2]
      have he : (b f : A) * ((b g : A) * z) = (b (f * g) : A) * z := by
        rw [map_mul, Units.val_mul, mul_assoc]
      rw [he]

private def proj (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) : E a b h →* F × F where
  toFun x := (x.left.right, x.right)
  map_one' := rfl
  map_mul' x y := by
    refine Prod.ext ?_ rfl
    exact congrArg (x.left.right * ·) ((twists_properties a b h x.right).1 y.left)

private abbrev incl (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) :
    Multiplicative A →* E a b h :=
  SemidirectProduct.inl.comp SemidirectProduct.inl

private theorem incl_injective (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) :
    Function.Injective (incl a b h) :=
  SemidirectProduct.inl_injective.comp SemidirectProduct.inl_injective

private theorem proj_surjective (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) :
    Function.Surjective (proj a b h) :=
  fun ⟨f, g⟩ => ⟨⟨⟨1, f⟩, g⟩, rfl⟩

private theorem range_incl (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g)) :
    (incl a b h).range = (proj a b h).ker := by
  ext ⟨⟨x, f⟩, g⟩
  simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MonoidHom.mem_ker]
  change (∃ z, (⟨⟨z, 1⟩, 1⟩ : E a b h) = ⟨⟨x, f⟩, g⟩) ↔ (f, g) = (1, 1)
  constructor
  · rintro ⟨z, hz⟩
    exact (congrArg (proj a b h) hz).symm
  · intro hz
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hz
    exact ⟨x, rfl⟩

private theorem conj_incl (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g))
    (x : E a b h) (z : A) :
    x * incl a b h (ofAdd z) * x⁻¹ =
      incl a b h (ofAdd ((a x.left.right : A) * (b x.right : A) * z)) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine SemidirectProduct.ext (SemidirectProduct.ext ?_ ?_) ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    change (x.left * twists a b h x.right ⟨ofAdd z, 1⟩).left =
      ((⟨ofAdd _, 1⟩ : N a) * twists a b h 1 x.left).left
    rw [(twists_properties a b h x.right).2 z, map_one, MulAut.one_apply]
    apply toAdd.injective
    change x.left.left.toAdd + (a x.left.right : A) * ((b x.right : A) * z) =
      (a x.left.right : A) * (b x.right : A) * z +
        (↑(a 1) : A) * x.left.left.toAdd
    simp [mul_assoc, add_comm]
  · simp [incl, (twists_properties a b h x.right).1]
  · simp [incl]

private theorem split_eq (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g))
    (s : F × F →* E a b h) (hs : ∀ fg, proj a b h (s fg) = fg)
    (i j : Bool) :
    let u := (s (FreeGroup.of i, 1)).left.left.toAdd
    let v := (s (1, FreeGroup.of j)).left.left.toAdd
    ((a (FreeGroup.of i) : A) - 1) * v - ((b (FreeGroup.of j) : A) - 1) * u =
      if i && j then 1 else 0 := by
  dsimp only
  let p := s (FreeGroup.of i, 1)
  let q := s (1, FreeGroup.of j)
  have hp : p.left.right = FreeGroup.of i ∧ p.right = 1 := Prod.ext_iff.mp (hs _)
  have hq : q.left.right = 1 ∧ q.right = FreeGroup.of j := Prod.ext_iff.mp (hs _)
  have hcomm : p * q = q * p := by
    dsimp [p, q]
    rw [← map_mul, ← map_mul]
    simp
  have he := congrArg (fun x : E a b h => x.left.left.toAdd) hcomm
  change (p.left * twists a b h p.right q.left).left.toAdd =
    (q.left * twists a b h q.right p.left).left.toAdd at he
  rw [hp.2, hq.2, map_one, MulAut.one_apply, twists_apply_of] at he
  change p.left.left.toAdd + (a p.left.right : A) * q.left.left.toAdd =
    q.left.left.toAdd + (a q.left.right : A) *
      ((b (FreeGroup.of j) : A) * p.left.left.toAdd +
        defect a (fun i => if i && j then 1 else 0) p.left.right) at he
  rw [hp.1, hq.1, map_one, Units.val_one, one_mul, defect_of] at he
  change ((a (FreeGroup.of i) : A) - 1) * q.left.left.toAdd -
    ((b (FreeGroup.of j) : A) - 1) * p.left.left.toAdd = _
  rw [sub_mul, sub_mul, one_mul, one_mul]
  rw [sub_eq_iff_eq_add]
  apply (add_left_inj (a := p.left.left.toAdd + q.left.left.toAdd)).mp
  calc
    _ = p.left.left.toAdd + (a (FreeGroup.of i) : A) * q.left.left.toAdd := by abel
    _ = _ := he.trans (by abel)

private theorem no_section (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g))
    (ha : Function.Injective a) (hb : Function.Injective b)
    (s : F × F →* E a b h) (hs : ∀ fg, proj a b h (s fg) = fg) : False := by
  let u (i : Bool) := (s (FreeGroup.of i, 1)).left.left.toAdd
  let v (j : Bool) := (s (1, FreeGroup.of j)).left.left.toAdd
  let p (i : Bool) := (a (FreeGroup.of i) : A) - 1
  let q (j : Bool) := (b (FreeGroup.of j) : A) - 1
  have he (i j : Bool) :
      p i * v j - q j * u i = if i && j then 1 else 0 := split_eq a b h s hs i j
  have hp : p false ≠ 0 := by
    intro hz
    apply FreeGroup.of_ne_one false
    apply ha
    rw [map_one]
    exact Units.ext (sub_eq_zero.mp hz)
  have hq : q false ≠ 0 := by
    intro hz
    apply FreeGroup.of_ne_one false
    apply hb
    rw [map_one]
    exact Units.ext (sub_eq_zero.mp hz)
  have hcomm (i j : Bool) : Commute (p i) (q j) :=
    (((h (FreeGroup.of i) (FreeGroup.of j)).units_val.sub_left (Commute.one_left _)).sub_right
      (Commute.one_right _))
  let t := (p false)⁻¹ * u false
  have ht : p false * t = u false := by simp [t, hp]
  have hv (j : Bool) : v j = q j * t := by
    apply mul_left_cancel₀ hp
    calc
      p false * v j = q j * u false := sub_eq_zero.mp (by simpa using he false j)
      _ = p false * (q j * t) := by simp only [← ht, ← mul_assoc, (hcomm false j).eq]
  have hu : u true = p true * t := by
    apply mul_left_cancel₀ hq
    calc
      q false * u true = p true * v false := (sub_eq_zero.mp (by simpa using he true false)).symm
      _ = q false * (p true * t) := by simp only [hv, ← mul_assoc, (hcomm true false).eq]
  have hfin := he true true
  simp only [hv, hu, ← mul_assoc, (hcomm true true).eq, sub_self] at hfin
  exact zero_ne_one hfin

private theorem refute_of_embedding
    (a b : F →* Aˣ) (h : ∀ f g, Commute (a f) (b g))
    (hemb : Function.Injective (MonoidHom.noncommCoprod a b h)) :
    ¬ divisionRingMultiplicationExtensionsSplit := by
  let m := MonoidHom.noncommCoprod a b h
  let em := MulEquiv.ofBijective m.rangeRestrict
    ⟨fun _ _ h => hemb (congrArg Subtype.val h), m.rangeRestrict_surjective⟩
  let π := em.toMonoidHom.comp (proj a b h)
  intro hh
  obtain ⟨s, hs⟩ := hh A m.range (E a b h) (incl a b h) π
    (incl_injective a b h) (em.surjective.comp (proj_surjective a b h))
    (by rw [range_incl]; ext x; simp [π, MonoidHom.mem_ker])
    (conj_incl a b h)
  obtain ⟨ha, hb, _⟩ := (MonoidHom.noncommCoprod_injective a b h).mp hemb
  exact no_section a b h ha hb (s.comp em.toMonoidHom) fun g => em.injective (hs (em g))




end Extension

/-! ## Ore fractions of skew polynomials

The lexicographically greatest exponent proves that the
skew monoid algebra is a domain. The dimension of the space of polynomials supported in a
square of exponents gives the Ore condition by counting unknowns and equations.
-/

open SkewMonoidAlgebra
open scoped Pointwise nonZeroDivisors

private abbrev M := Multiplicative (ℕ ×ₗ ℕ)

section Domain

variable {K : Type} [Ring K] [IsDomain K]
variable [MulSemiringAction M K]
variable (hinj : ∀ (m : M), Function.Injective ((m • ·) : K → K))

private abbrev Skew (K : Type) [Zero K] := SkewMonoidAlgebra K M

omit [IsDomain K] [MulSemiringAction M K] in
private theorem support_nonempty {x : Skew K} (hx : x ≠ 0) : x.support.Nonempty := by
  contrapose! hx
  simpa using hx

include hinj in
private theorem skew_mul_ne_zero {x y : Skew K} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  classical
  let a := x.support.max' (support_nonempty hx)
  let b := y.support.max' (support_nonempty hy)
  have ha : a ∈ x.support := Finset.max'_mem _ _
  have hb : b ∈ y.support := Finset.max'_mem _ _
  have sole (i : M) (hi : i ∈ x.support) (j : M) (hj : j ∈ y.support)
      (hij : i * j = a * b) : i = a ∧ j = b := by
    have hi' : i ≤ a := Finset.le_max' _ _ hi
    have hj' : j ≤ b := Finset.le_max' _ _ hj
    constructor
    · by_contra he
      exact (ne_of_lt (mul_lt_mul_of_lt_of_le (lt_of_le_of_ne hi' he) hj')) hij
    · by_contra he
      exact (ne_of_lt (mul_lt_mul_of_le_of_lt hi' (lt_of_le_of_ne hj' he))) hij
  have hc : (x * y).coeff (a * b) = x.coeff a * a • y.coeff b := by
    rw [SkewMonoidAlgebra.coeff_mul]
    change ∑ i ∈ x.support, (∑ j ∈ y.support,
      if i * j = a * b then x.coeff i * i • y.coeff j else 0) = _
    rw [Finset.sum_eq_single_of_mem a ha]
    · rw [Finset.sum_eq_single_of_mem b hb]
      · simp
      · intro j hj hjb
        exact ite_eq_right fun hij => hjb (sole a ha j hj hij).2
    · intro i hi hia
      apply Finset.sum_eq_zero
      intro j hj
      exact ite_eq_right fun hij => hia (sole i hi j hj hij).1
  intro he
  rw [he, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (mul_ne_zero (mem_support_iff.mp ha)
    (fun hz => mem_support_iff.mp hb (hinj a (hz.trans (smul_zero _).symm)))) hc.symm

private def box (n : ℕ) : Set M :=
  {m | (ofLex m.toAdd).1 < n ∧ (ofLex m.toAdd).2 < n}

private def boxEquiv (n : ℕ) : box n ≃ Fin n × Fin n where
  toFun x := (⟨(ofLex x.1.toAdd).1, x.2.1⟩, ⟨(ofLex x.1.toAdd).2, x.2.2⟩)
  invFun x := ⟨Multiplicative.ofAdd (toLex (x.1.val, x.2.val)), x.1.isLt, x.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsDomain K] [MulSemiringAction M K] in
private theorem support_subset_box (x y : Skew K) :
    ∃ n : ℕ, (x.support : Set M) ⊆ box n ∧ (y.support : Set M) ⊆ box n := by
  classical
  let size : M → ℕ := fun m => max (ofLex m.toAdd).1 (ofLex m.toAdd).2
  let n := ((x.support ∪ y.support).image size).sup id + 1
  have hd {i : M} (hi : i ∈ x.support ∪ y.support) : i ∈ box n := by
    have h := Finset.le_sup (f := id) (Finset.mem_image_of_mem size hi)
    have hlt : size i < n := Nat.lt_succ_of_le h
    change (ofLex i.toAdd).1 < n ∧ (ofLex i.toAdd).2 < n
    have h₁ := le_max_left (ofLex i.toAdd).1 (ofLex i.toAdd).2
    have h₂ := le_max_right (ofLex i.toAdd).1 (ofLex i.toAdd).2
    dsimp only [size] at hlt
    omega
  exact ⟨n, fun _ hi => hd (Finset.mem_union_left _ hi),
    fun _ hi => hd (Finset.mem_union_right _ hi)⟩

omit [IsDomain K] in
private theorem mul_support_subset_box {x y : Skew K} {m n : ℕ}
    (hx : (x.support : Set M) ⊆ box m) (hy : (y.support : Set M) ⊆ box n) :
    ((x * y).support : Set M) ⊆ box (m + n) := by
  rintro _ hs
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp (support_mul x y hs)
  obtain ⟨h₁, h₂⟩ := hx hu
  obtain ⟨h₃, h₄⟩ := hy hv
  change (ofLex u.toAdd).1 + (ofLex v.toAdd).1 < m + n ∧
    (ofLex u.toAdd).2 + (ofLex v.toAdd).2 < m + n
  omega

include hinj in
private theorem skew_noZeroDivisors : NoZeroDivisors (Skew K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    by_contra! hne
    exact skew_mul_ne_zero hinj hne.1 hne.2 h

end Domain

section Ore

variable {K : Type} [DivisionRing K] [MulSemiringAction M K]
variable (hinj : ∀ (m : M), Function.Injective ((m • ·) : K → K))

private noncomputable def boxSpace (n : ℕ) : Submodule K (Skew K) :=
  (Finsupp.supported K K (box n)).comap (coeffLinearEquiv (S := K) (k := K) (G := M)).toLinearMap

private noncomputable def boxSpaceEquiv (n : ℕ) : boxSpace (K := K) n ≃ₗ[K] (box n →₀ K) :=
  (LinearEquiv.ofSubmodules
    (coeffLinearEquiv (S := K) (k := K) (G := M)) (boxSpace (K := K) n)
    (Finsupp.supported K K (box n)) (Submodule.map_comap_eq_of_surjective
      (coeffLinearEquiv (S := K) (k := K) (G := M)).surjective _)) ≪≫ₗ
    Finsupp.supportedEquivFinsupp (box n)

omit [MulSemiringAction M K] in
private theorem boxSpace_finrank (n : ℕ) : Module.finrank K (boxSpace (K := K) n) = n * n := by
  let _ := Fintype.ofEquiv (Fin n × Fin n) (boxEquiv n).symm
  rw [(boxSpaceEquiv (K := K) n).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_congr (boxEquiv n), Fintype.card_prod, Fintype.card_fin]

private noncomputable def rproduct {m n : ℕ} (a : Skew K) (ha : a ∈ boxSpace (K := K) n) :
    boxSpace (K := K) m →ₗ[K] boxSpace (K := K) (m + n) where
  toFun x := ⟨x.1 * a, mul_support_subset_box
    x.2 ha⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

include hinj in
private theorem skew_oreCondition (r : Skew K) (s : (Skew K)⁰) :
    ∃ (r' : Skew K) (s' : (Skew K)⁰), s' * r = r' * s := by
  let _ := skew_noZeroDivisors hinj
  by_cases hr : r = 0
  · exact ⟨0, 1, by simp [hr]⟩
  have hs : (s : Skew K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  obtain ⟨n, hrn, hsn⟩ := support_subset_box r (s : Skew K)
  let m := 3 * n + 1
  let f : boxSpace (K := K) m × boxSpace (K := K) m →ₗ[K] boxSpace (K := K) (m + n) :=
    (rproduct r hrn).coprod (-(rproduct (s : Skew K) hsn))
  let _ := Fintype.ofEquiv (Fin (m + n) × Fin (m + n)) (boxEquiv (m + n)).symm
  let _ := Fintype.ofEquiv (Fin m × Fin m) (boxEquiv m).symm
  let _ : Module.Finite K (boxSpace (K := K) m) :=
    Module.Finite.equiv (boxSpaceEquiv (K := K) m).symm
  let _ : Module.Finite K (boxSpace (K := K) (m + n)) :=
    Module.Finite.equiv (boxSpaceEquiv (K := K) (m + n)).symm
  have hni : ¬Function.Injective f := by
    intro h
    have hd := f.finrank_le_finrank_of_injective h
    rw [Module.finrank_prod, boxSpace_finrank, boxSpace_finrank] at hd
    dsimp only [m] at hd
    nlinarith
  have hker := mt LinearMap.ker_eq_bot.mp hni
  obtain ⟨⟨p, q⟩, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have he : p.1 * r = q.1 * (s : Skew K) := by
    have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    exact sub_eq_zero.mp hz
  have hp : p.1 ≠ 0 := by
    intro hp
    have hq : q.1 = 0 := (mul_eq_zero.mp (by simpa [hp] using he.symm)).resolve_right hs
    exact hne (Prod.ext (Subtype.ext hp) (Subtype.ext hq))
  exact ⟨q.1, ⟨p.1, mem_nonZeroDivisors_of_ne_zero hp⟩, he⟩

end Ore

/-! ## Two commuting copies of the free group

Each exponent acts by changing the sign of the
corresponding coefficient variable. Specializing one variable to diagonal entries and its
skew variable to the swap matrix sends the generators to free transvections. The two copies
commute because the sign changes and the coefficient variables are independent.
-/

noncomputable section

open OreLocalization SkewMonoidAlgebra
open scoped nonZeroDivisors Matrix Pointwise

private abbrev P := MvPolynomial Bool ℚ
private abbrev K := FractionRing P
private abbrev R := SkewMonoidAlgebra P M
private abbrev S := SkewMonoidAlgebra K M

private def degree (m : M) (i : Bool) : ℕ :=
  if i then (ofLex m.toAdd).2 else (ofLex m.toAdd).1

private theorem degree_mul (m n : M) (i : Bool) :
    degree (m * n) i = degree m i + degree n i := by
  cases i <;> rfl

private def step (i : Bool) : M :=
  Multiplicative.ofAdd (toLex (if i then (0, 1) else (1, 0)))

private theorem degree_step (i j : Bool) : degree (step i) j = if i = j then 1 else 0 := by
  cases i <;> cases j <;> rfl

private def sign (m : M) (i : Bool) : ℚ := (-1) ^ degree m i

private theorem sign_mul (m n : M) (i : Bool) : sign (m * n) i = sign m i * sign n i := by
  simp [sign, degree_mul, pow_add]

private theorem sign_sq (m : M) (i : Bool) : sign m i * sign m i = 1 := by
  rw [sign, ← mul_pow]
  norm_num

private def flipHom (m : M) : P →ₐ[ℚ] P :=
  MvPolynomial.aeval fun i => MvPolynomial.C (sign m i) * MvPolynomial.X i

private theorem flipHom_X (m : M) (i : Bool) :
    flipHom m (MvPolynomial.X i) = MvPolynomial.C (sign m i) * MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

private theorem flipHom_mul (m n : M) : flipHom (m * n) = (flipHom m).comp (flipHom n) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [flipHom_X, AlgHom.comp_apply, map_mul, MvPolynomial.C_eq_algebraMap, AlgHom.commutes,
    sign_mul]
  change (algebraMap ℚ P) (sign m i) * (algebraMap ℚ P) (sign n i) *
    MvPolynomial.X i = (algebraMap ℚ P) (sign n i) *
      ((algebraMap ℚ P) (sign m i) * MvPolynomial.X i)
  ac_rfl

private theorem flipHom_one : flipHom 1 = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  have h : degree 1 i = 0 := by cases i <;> rfl
  simp [flipHom_X, sign, h]

private theorem flipHom_involutive (m : M) : Function.Involutive (flipHom m) := by
  have h : (flipHom m).comp (flipHom m) = AlgHom.id ℚ P := by
    rw [← flipHom_mul]
    apply MvPolynomial.algHom_ext
    intro i
    simp [flipHom_X, sign_mul, sign_sq]
  exact fun x => DFunLike.congr_fun h x

private def flips : M →* RingAut P where
  toFun m :=
    { (flipHom m).toRingHom with
      invFun := flipHom m
      left_inv := flipHom_involutive m
      right_inv := flipHom_involutive m }
  map_one' := RingEquiv.ext (fun x => DFunLike.congr_fun flipHom_one x)
  map_mul' m n := RingEquiv.ext (fun x => DFunLike.congr_fun (flipHom_mul m n) x)

private noncomputable def fractionFlips : M →* RingAut K :=
  (IsFractionRing.ringEquivOfRingEquivHom P K).comp flips

private local instance polyAction : MulSemiringAction M P := MulSemiringAction.compHom P flips

private noncomputable local instance fracAction : MulSemiringAction M K :=
  MulSemiringAction.compHom K fractionFlips

private theorem frac_smul_injective (m : M) : Function.Injective ((m • ·) : K → K) :=
  (fractionFlips m).injective

private theorem fractionMap_flip (m : M) (x : P) :
    algebraMap P K (m • x) = m • algebraMap P K x :=
  (IsFractionRing.ringEquivOfRingEquiv_algebraMap (flips m) x).symm

private noncomputable def toFracSkew : R →+* S :=
  liftNCRingHom (singleOneRingHom.comp (algebraMap P K)) (SkewMonoidAlgebra.of K M) (by
    intro p m
    simp only [RingHom.comp_apply, SkewMonoidAlgebra.of_apply]
    change single 1 (algebraMap P K (m • p)) * single m 1 =
      single m 1 * single 1 (algebraMap P K p)
    simp [single_mul_single, fractionMap_flip])

private theorem toFracSkew_single (m : M) (p : P) :
    toFracSkew (single m p) = single m (algebraMap P K p) := by
  change liftNC _ _ (single m p) = _
  simp [liftNC_single, singleOneRingHom, SkewMonoidAlgebra.of_apply, single_mul_single]

private theorem toFracSkew_coeff (x : R) (m : M) :
    (toFracSkew x).coeff m = algebraMap P K (x.coeff m) := by
  classical
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i p => by_cases h : i = m <;> simp [h, toFracSkew_single, coeff_single]

private theorem toFracSkew_inj : Function.Injective toFracSkew := by
  intro x y h
  apply coeff_injective
  apply Finsupp.ext
  intro m
  apply IsFractionRing.injective P K
  rw [← toFracSkew_coeff x, ← toFracSkew_coeff y, h]

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℚ
private abbrev Col := Matrix (Fin 2) (Fin 1) ℚ

private def transvection (j : Bool) (t : ℚ) : Mat :=
  if j then Matrix.transvection 1 0 t else Matrix.transvection 0 1 t

private theorem transvection_zero (j : Bool) : transvection j 0 = 1 := by
  cases j <;> simp [transvection]

private theorem transvection_add (j : Bool) (a b : ℚ) :
    transvection j (a + b) = transvection j a * transvection j b := by
  cases j <;> simp [transvection, Matrix.transvection_mul_transvection_same]

private def transvections (j : Bool) : Multiplicative ℤ →* Matˣ where
  toFun n :=
    { val := transvection j (2 * (n.toAdd : ℚ))
      inv := transvection j (-(2 * (n.toAdd : ℚ)))
      val_inv := by rw [← transvection_add, add_neg_cancel, transvection_zero]
      inv_val := by rw [← transvection_add, neg_add_cancel, transvection_zero] }
  map_one' := Units.ext (by change transvection j (2 * (0 : ℤ)) = 1; simp [transvection_zero])
  map_mul' x y := Units.ext (by
    change transvection j (2 * (((x.toAdd + y.toAdd : ℤ) : ℚ))) = _
    rw [Int.cast_add, mul_add, transvection_add]
    rfl)

private def cone (i : Bool) : Set Col :=
  {v | if i then |v 0 0| < |v 1 0| else |v 1 0| < |v 0 0|}

private theorem move_cone (x y : ℚ) (h : |x| < |y|) (n : ℤ) (hn : n ≠ 0) :
    |y| < |x + 2 * (n : ℚ) * y| := by
  have hn' : (1 : ℤ) ≤ |n| := by
    have := abs_pos.mpr hn
    omega
  have hnq : (1 : ℚ) ≤ |(n : ℚ)| := by exact_mod_cast hn'
  have hbig : 2 * |y| ≤ |2 * (n : ℚ) * y| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
    gcongr
    linarith
  have ht := abs_add_le (x + 2 * (n : ℚ) * y) (-x)
  rw [add_comm x, add_assoc, add_neg_cancel, add_zero, abs_neg] at ht
  rw [add_comm (2 * (n : ℚ) * y) x] at ht
  linarith

private theorem matrix_free :
    Function.Injective
      (FreeGroup.lift (fun j : Bool => transvections j (Multiplicative.ofAdd 1))) := by
  let exponent : FreeGroup Unit →* Multiplicative ℤ :=
    FreeGroup.lift fun _ => Multiplicative.ofAdd 1
  have exp_eq (w : FreeGroup Unit) :
      (exponent w).toAdd = FreeGroup.freeGroupUnitEquivInt w := by
    let count : FreeGroup Unit →* Multiplicative ℤ :=
      FreeGroup.prod.comp (FreeGroup.map fun _ => Multiplicative.ofAdd (1 : ℤ))
    have h : exponent = count := FreeGroup.ext_hom _ _ (by intro u; simp [exponent, count])
    rw [h]
    rfl
  let f (i : Bool) : FreeGroup Unit →* Matˣ := (transvections i).comp exponent
  have hhom : FreeGroup.lift (fun j : Bool => transvections j (Multiplicative.ofAdd 1)) =
      (Monoid.CoprodI.lift f).comp (@freeGroupEquivCoprodI Bool).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    simp [f, exponent]
  rw [hhom]
  refine (Monoid.CoprodI.lift_injective_of_ping_pong f ?_ cone ?_ ?_ ?_).comp
    freeGroupEquivCoprodI.injective
  · right
    refine ⟨false, ?_⟩
    rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
    exact Cardinal.natCast_le_aleph0
  · intro i
    cases i
    · exact ⟨!![1; 0], by norm_num [cone]⟩
    · exact ⟨!![0; 1], by norm_num [cone]⟩
  · intro i j hij
    change Disjoint (cone i) (cone j)
    rw [Set.disjoint_left]
    intro v hi hj
    cases i <;> cases j <;> simp_all [cone, not_lt_of_gt]
  · intro i j hij w hw
    let n := (exponent w).toAdd
    have hn : n ≠ 0 := by
      intro he
      apply hw
      apply FreeGroup.freeGroupUnitEquivInt.injective
      rw [← exp_eq, ← exp_eq, map_one]
      exact he
    rintro _ ⟨v, hv, rfl⟩
    have smul_coord (k : Fin 2) :
        (f i w • v) k 0 = (transvection i (2 * (n : ℚ))) k 0 * v 0 0 +
          (transvection i (2 * (n : ℚ))) k 1 * v 1 0 := by
      change (transvection i (2 * (n : ℚ)) * v) k 0 = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    cases i <;> cases j <;> simp_all only [ne_eq, not_true_eq_false, cone, Set.mem_ofPred_eq,
      Bool.false_eq_true, Bool.true_eq, ite_true, ite_false]
    · simpa [transvection, Matrix.transvection, Matrix.single_apply] using
        move_cone (v 0 0) (v 1 0) hv n hn
    · simpa [transvection, Matrix.transvection, Matrix.single_apply, add_comm] using
        move_cone (v 1 0) (v 0 0) hv n hn

private def swap : Mat := !![0, 1; 1, 0]

private theorem swap_sq : swap ^ 2 = 1 := by
  rw [pow_two]
  ext x y
  fin_cases x <;> fin_cases y <;> norm_num [swap, Matrix.mul_apply, Fin.sum_univ_two]

private def orientation (j : Fin 2) : ℚ := if j = 0 then 1 else -1

private def assignment (i : Bool) (j : Fin 2) (k : Bool) : ℚ :=
  if k = i then orientation j else 0

private def evalDiag (i : Bool) : P →+* Mat :=
  (Matrix.diagonalRingHom (Fin 2) ℚ).comp
    (RingHom.pi fun j => MvPolynomial.eval (assignment i j))

private def evalMonomial (i : Bool) : M →* Mat where
  toFun m := swap ^ degree m i
  map_one' := by
    have h : degree 1 i = 0 := by cases i <;> rfl
    change swap ^ degree 1 i = 1
    rw [h, pow_zero]
  map_mul' m n := by
    change swap ^ degree (m * n) i = swap ^ degree m i * swap ^ degree n i
    rw [degree_mul, pow_add]

private theorem eval_flip_of (i : Bool) (m : M) (s t : Fin 2)
    (h : orientation t = sign m i * orientation s) (p : P) :
    MvPolynomial.eval (assignment i s) (m • p) = MvPolynomial.eval (assignment i t) p := by
  have he : (MvPolynomial.eval (assignment i s)).comp (flipHom m).toRingHom =
      MvPolynomial.eval (assignment i t) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      change MvPolynomial.eval (assignment i s) (flipHom m (MvPolynomial.C q)) =
        MvPolynomial.eval (assignment i t) (MvPolynomial.C q)
      have hq : flipHom m (MvPolynomial.C q) = MvPolynomial.C q := by
        rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
      rw [hq, MvPolynomial.eval_C, MvPolynomial.eval_C]
    · intro k
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, flipHom_X,
        map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, assignment]
      by_cases hk : k = i
      · subst k
        simp [h]
      · simp [hk]
  exact DFunLike.congr_fun he p

private theorem eval_compatible (i : Bool) (m : M) (p : P) :
    evalDiag i (m • p) * evalMonomial i m = evalMonomial i m * evalDiag i p := by
  rcases Nat.even_or_odd' (degree m i) with ⟨d, hd | hd⟩
  · have hsign : sign m i = 1 := by simp [sign, hd, pow_mul]
    have hn : evalMonomial i m = 1 := by
      change swap ^ degree m i = 1
      simp [hd, pow_mul, swap_sq]
    have hc (j : Fin 2) := eval_flip_of i m j j (by simp [hsign]) p
    simp only [hn, mul_one, one_mul, evalDiag, RingHom.comp_apply, Matrix.diagonalRingHom_apply]
    exact congrArg Matrix.diagonal (funext hc)
  · have hsign : sign m i = -1 := by simp [sign, hd, pow_add, pow_mul]
    have hn : evalMonomial i m = swap := by
      change swap ^ degree m i = swap
      simp [hd, pow_add, pow_mul, swap_sq]
    have hc0 := eval_flip_of i m 0 1 (by norm_num [orientation, hsign]) p
    have hc1 := eval_flip_of i m 1 0 (by norm_num [orientation, hsign]) p
    ext j k
    fin_cases j <;> fin_cases k
    · simp [evalDiag, hn, Matrix.mul_apply, Fin.sum_univ_two, swap]
    · simpa [evalDiag, hn, Matrix.mul_apply, Fin.sum_univ_two, swap, RingHom.pi_apply] using hc0
    · simpa [evalDiag, hn, Matrix.mul_apply, Fin.sum_univ_two, swap, RingHom.pi_apply] using hc1
    · simp [evalDiag, hn, Matrix.mul_apply, Fin.sum_univ_two, swap]

private def evalSkew (i : Bool) : R →+* Mat :=
  liftNCRingHom (evalDiag i) (evalMonomial i) (fun {_ _} => eval_compatible i _ _)

private theorem evalSkew_single (i : Bool) (m : M) (p : P) :
    evalSkew i (single m p) = evalDiag i p * evalMonomial i m := by
  exact liftNC_single _ _ _ _

private def coefficient (i j : Bool) : P :=
  if j then 1 - MvPolynomial.X i else 1 + MvPolynomial.X i

private def offset (i j : Bool) : R := single (step i) (coefficient i j)

private def numerator (i j : Bool) : R := 1 + offset i j

private def centralCoeff (i : Bool) : P := 1 - (MvPolynomial.X i)^2

private def centralDenom (i : Bool) : R := 1 - single (step i ^ 2) (centralCoeff i)

private theorem action_X (m : M) (i : Bool) :
    m • (MvPolynomial.X i : P) = MvPolynomial.C (sign m i) * MvPolynomial.X i :=
  flipHom_X m i

private theorem action_centralCoeff (m : M) (i : Bool) :
    m • centralCoeff i = centralCoeff i := by
  have h : (sign m i)^2 = 1 := by simpa [pow_two] using sign_sq m i
  simp [centralCoeff, smul_sub, smul_pow', action_X, mul_pow, ← map_pow, h]

private theorem action_even (m : M) (p : P) : m ^ 2 • p = p := by
  have h : flipHom (m ^ 2) = AlgHom.id ℚ P := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [flipHom_X, pow_two, sign_mul, sign_sq]
  exact DFunLike.congr_fun h p

private theorem centralDenom_commute (i : Bool) (x : R) : Commute (centralDenom i) x := by
  apply (Commute.one_left x).sub_left
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => exact Commute.zero_right _
  | add x y hx hy => exact hx.add_right hy
  | single m p =>
    change single (step i ^ 2) (centralCoeff i) * single m p =
      single m p * single (step i ^ 2) (centralCoeff i)
    rw [single_mul_single, single_mul_single, action_even, action_centralCoeff,
      mul_comm (step i ^ 2), mul_comm (centralCoeff i)]

private theorem offset_sq (i j : Bool) : offset i j ^ 2 = single (step i ^ 2) (centralCoeff i) := by
  rw [pow_two, offset, single_mul_single, ← pow_two]
  congr 1
  cases j <;>
    simp [coefficient, smul_sub, smul_add, action_X, sign, degree_step, centralCoeff] <;> ring

private theorem numerator_mul_conj (i j : Bool) :
    numerator i j * (1 - offset i j) = centralDenom i := by
  simp only [numerator, centralDenom, add_mul, mul_sub, mul_one, one_mul]
  rw [← offset_sq, pow_two]
  abel

private theorem conj_mul_numerator (i j : Bool) :
    (1 - offset i j) * numerator i j = centralDenom i := by
  simp only [numerator, centralDenom, mul_add, sub_mul, mul_one, one_mul]
  rw [← offset_sq, pow_two]
  abel

private theorem numerator_commute (i k j l : Bool) (h : i ≠ k) :
    Commute (numerator i j) (numerator k l) := by
  apply (Commute.one_left _).add_left
  apply (Commute.one_right _).add_right
  have hf : step i • coefficient k l = coefficient k l := by
    cases l <;> simp [coefficient, smul_add, smul_sub, action_X, sign, degree_step, h]
  have hg : step k • coefficient i j = coefficient i j := by
    cases j <;> simp [coefficient, smul_add, smul_sub, action_X, sign, degree_step, h.symm]
  change single (step i) (coefficient i j) * single (step k) (coefficient k l) =
    single (step k) (coefficient k l) * single (step i) (coefficient i j)
  rw [single_mul_single, single_mul_single, hf, hg, mul_comm (step i), mul_comm (coefficient i j)]

private theorem eval_centralDenom (i : Bool) : evalSkew i (centralDenom i) = 1 := by
  have hz : evalDiag i (centralCoeff i) = 0 := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      norm_num [evalDiag, centralCoeff, assignment, orientation, RingHom.pi_apply]
  rw [centralDenom, map_sub, map_one, evalSkew_single, hz, zero_mul, sub_zero]

private theorem eval_numerator (i j : Bool) :
    evalSkew i (numerator i j) = (transvections j (Multiplicative.ofAdd 1) : Mat) := by
  change _ = transvection j (2 * ((1 : ℤ) : ℚ))
  rw [numerator, map_add, map_one, offset, evalSkew_single]
  cases j <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    norm_num [evalDiag, evalMonomial, degree_step, assignment, coefficient, orientation, swap,
      transvection, Matrix.transvection, Matrix.single_apply, Matrix.mul_apply, Fin.sum_univ_two,
      RingHom.pi_apply]

private local instance skewDomain : NoZeroDivisors S := skew_noZeroDivisors frac_smul_injective

private local instance fullOre : OreSet S⁰ :=
  Classical.choice <|
    nonempty_oreSet_iff_of_noZeroDivisors.mpr (skew_oreCondition frac_smul_injective)

private abbrev D := S[S⁰⁻¹]

private def embed : R →+* D :=
  OreLocalization.numeratorRingHom.comp toFracSkew

private theorem embed_injective : Function.Injective embed :=
  (OreLocalization.numeratorHom_inj (S := S⁰) inf_le_left).comp toFracSkew_inj

private abbrev denominators (i : Bool) := Submonoid.powers (centralDenom i)

private local instance polyDomain : NoZeroDivisors R :=
  skew_noZeroDivisors fun m => (flips m).injective

private local instance centralOre (i : Bool) : OreSet (denominators i) :=
  oreSetOfNoZeroDivisors (fun r _ => r) (fun _ s => s) (by
    intro r s
    obtain ⟨k, hk⟩ := s.2
    change (s : R) * r = r * (s : R)
    rw [← hk]
    exact ((centralDenom_commute i r).pow_left k).eq)

private abbrev Q (i : Bool) := R[(denominators i)⁻¹]

private theorem eval_denom (i : Bool) (s : denominators i) : evalSkew i s = 1 := by
  obtain ⟨k, hk⟩ := s.2
  rw [← hk, map_pow, eval_centralDenom, one_pow]

private def specialize (i : Bool) : Q i →+* Mat :=
  OreLocalization.universalHom (evalSkew i) 1 (eval_denom i)

private theorem denom_ne_zero (i : Bool) (s : denominators i) : (s : R) ≠ 0 := by
  intro h
  have he := eval_denom i s
  rw [h, map_zero] at he
  exact zero_ne_one he

private def denomUnits (i : Bool) : denominators i →* Dˣ where
  toFun s := Units.mk0 (embed s) (fun h => denom_ne_zero i s (embed_injective (h.trans
    (map_zero embed).symm)))
  map_one' := Units.ext (map_one embed)
  map_mul' s t := Units.ext (map_mul embed (s : R) (t : R))

private def locEmbed (i : Bool) : Q i →+* D :=
  OreLocalization.universalHom embed (denomUnits i) (fun _ => rfl)

private theorem locEmbed_injective (i : Bool) : Function.Injective (locEmbed i) := by
  apply (injective_iff_map_eq_zero _).2
  intro x
  induction x using OreLocalization.ind with
  | _ p s =>
    intro h
    change (↑((denomUnits i s)⁻¹) : D) * embed p = 0 at h
    rw [Units.mul_right_eq_zero] at h
    have hp : p = 0 := embed_injective (h.trans (map_zero embed).symm)
    simp [hp]

private def baseDenom (i : Bool) : denominators i := ⟨centralDenom i, ⟨1, pow_one _⟩⟩

private def fractionGenerator (i j : Bool) : (Q i)ˣ where
  val := OreLocalization.numeratorRingHom (numerator i j)
  inv := OreLocalization.numeratorRingHom (1 - offset i j) *
    ↑(OreLocalization.numeratorUnit (baseDenom i))⁻¹
  val_inv := by
    rw [← mul_assoc, ← map_mul, numerator_mul_conj]
    exact Units.mul_inv (OreLocalization.numeratorUnit (baseDenom i))
  inv_val := by
    let d : (Q i)ˣ := OreLocalization.numeratorUnit (baseDenom i)
    have hc : Commute (d : Q i) (OreLocalization.numeratorRingHom (numerator i j)) :=
      (centralDenom_commute i (numerator i j)).map OreLocalization.numeratorRingHom
    change (OreLocalization.numeratorRingHom (1 - offset i j) * (↑d⁻¹ : Q i)) *
        OreLocalization.numeratorRingHom (numerator i j) = 1
    rw [mul_assoc, hc.units_inv_left.eq, ← mul_assoc, ← map_mul, conj_mul_numerator]
    exact Units.mul_inv d

private def locFree (i : Bool) : FreeGroup Bool →* (Q i)ˣ :=
  FreeGroup.lift (fractionGenerator i)

private theorem locFree_inj (i : Bool) : Function.Injective (locFree i) := by
  have he : (Units.map (specialize i).toMonoidHom).comp (locFree i) =
      FreeGroup.lift (fun j : Bool => transvections j (Multiplicative.ofAdd 1)) := by
    apply FreeGroup.ext_hom
    intro j
    apply Units.ext
    simp only [locFree, MonoidHom.comp_apply, FreeGroup.lift_apply_of, Units.coe_map,
      RingHom.toMonoidHom_eq_coe]
    change specialize i (OreLocalization.numeratorHom (S := denominators i) (numerator i j)) = _
    exact (OreLocalization.universalHom_commutes _ _ _).trans (eval_numerator i j)
  intro x y h
  apply matrix_free
  rw [← he]
  exact congrArg (Units.map (specialize i).toMonoidHom) h

private def freeEmbedding (i : Bool) : FreeGroup Bool →* Dˣ :=
  (Units.map (locEmbed i).toMonoidHom).comp (locFree i)

private theorem freeEmbedding_inj (i : Bool) : Function.Injective (freeEmbedding i) :=
  (Units.map_injective (locEmbed_injective i)).comp (locFree_inj i)

private theorem coe_freeEmbedding_of (i j : Bool) :
    (freeEmbedding i (FreeGroup.of j) : D) = embed (numerator i j) := by
  simp only [freeEmbedding, locFree, MonoidHom.comp_apply, FreeGroup.lift_apply_of,
    Units.coe_map, RingHom.toMonoidHom_eq_coe]
  change locEmbed i (OreLocalization.numeratorHom (S := denominators i) (numerator i j)) = _
  exact OreLocalization.universalHom_commutes _ _ _

private theorem freeEmbedding_commute (f g : FreeGroup Bool) :
    Commute (freeEmbedding false f) (freeEmbedding true g) := by
  have on_generators (j l : Bool) :
      Commute (freeEmbedding false (FreeGroup.of j)) (freeEmbedding true (FreeGroup.of l)) := by
    apply Commute.units_of_val
    rw [coe_freeEmbedding_of, coe_freeEmbedding_of]
    exact (numerator_commute false true j l Bool.false_ne_true).map embed
  induction f using FreeGroup.induction_on with
  | one => simp
  | of j =>
    induction g using FreeGroup.induction_on with
    | one => simp
    | of l => exact on_generators j l
    | inv_of _ ih => simpa only [map_inv] using ih.inv_right
    | mul _ _ ih ih' => simpa only [map_mul] using ih.mul_right ih'
  | inv_of _ ih => simpa only [map_inv] using ih.inv_left
  | mul _ _ ih ih' => simpa only [map_mul] using ih.mul_left ih'

private theorem coprod_inj :
    Function.Injective
      (MonoidHom.noncommCoprod (freeEmbedding false) (freeEmbedding true)
        freeEmbedding_commute) := by
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  refine ⟨freeEmbedding_inj false, freeEmbedding_inj true, ?_⟩
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  have hcentral : a ∈ Subgroup.center (FreeGroup Bool) := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply freeEmbedding_inj false
    rw [map_mul, map_mul, ← hb]
    exact (freeEmbedding_commute g b).eq
  rw [FreeGroup.center_eq_bot_of_nontrivial] at hcentral
  simp [Subgroup.mem_bot.mp hcentral]

/--
**Extensions of a division ring's additive group by units need not split (Kourovka 18.76).**
There exist a division ring $A$, a subgroup $G$ of its unit group $A^\times$, a group $E$, an
injective homomorphism $i$ from the additive group of $A$ to $E$ and a surjective homomorphism
$\pi : E \to G$ whose kernel is the image of $i$, with $e \, i(a) \, e^{-1} = i(\pi(e) a)$ for all
$e \in E$ and $a \in A$, such that no homomorphism $s : G \to E$ satisfies $\pi(s(g)) = g$ for all
$g \in G$. That is, the splitting statement of Kourovka Problem 18.76 is false.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.76 (E. A. Palyutin); resolution: M.
Kinyon and J. Urban, Results on problems from the Kourovka Notebook, preprint, version 4, 19
September 2026; Achyuth Jayadevan, preprint of 14 September 2026,
https://zenodo.org/records/22751423, Kinyon-Urban Section 3.28: G = F × L with F, L free of rank 2,
D the division closure of kG in a Mal'cev-Neumann division ring (k = Q or a prime field), and a
nonsplit extension of (D, +) by G whose conjugation action on the kernel is left multiplication; AI
solutions confirmed by B. A. F. Wehrfritz, accepted in the Kourovka Notebook (21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem divisionRingMultiplicationExtensionsSplit_refuted :
    ¬ divisionRingMultiplicationExtensionsSplit :=
  refute_of_embedding (A := D) (freeEmbedding false) (freeEmbedding true)
    freeEmbedding_commute coprod_inj

end

end MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76Wanted
