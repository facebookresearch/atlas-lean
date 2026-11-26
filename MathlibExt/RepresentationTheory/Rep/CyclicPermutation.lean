/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Character-twisted cyclic permutation representations

Let k be a commutative ring, G a group, A a k-representation and
χ:G→Multiplicative(ZMod ℓ). The function module Pχ(A)=ZMod ℓ→A
has action (g•p)(i)=g•p(i+χ_add(g)).
The ring, group and coefficient universes are independent.

The diagonal δ(a) is the constant function a, for every ℓ.
For nonzero ℓ, the augmentation ε(p)=∑_i p(i) is equivariant and
ε∘δ=ℓ•id_A. For coefficients over ZMod 2 at ℓ=2, this gives the
short exact sequence A→Pχ(A)→A with diagonal and coordinate sum.
No surjectivity assumption on χ is needed for that sequence.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace Rep

universe uK uG uA

variable {k : Type uK} {G : Type uG} [CommRing k] [Group G]

/-- Let k be a commutative ring, G a group, A a k-linear
G-representation and χ:G→Multiplicative(ZMod ℓ) a character.
Write χ_add(g) for its additive ZMod ℓ value and
Pχ(A)=ZMod ℓ→A, with (g•p)(i)=g•p(i+χ_add(g)).
This is the k-linear permutation representation Pχ(A) with the
given simultaneous value action and positive index translation.
It is defined for every ℓ, including ℓ=0. -/
noncomputable abbrev cyclicPermutation
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (A : Rep.{uA} k G) : Rep.{uA} k G :=
  Rep.of
    { toFun := fun g =>
        { toFun := fun (f : ZMod ell → A) i =>
            A.ρ g (f (i + Multiplicative.toAdd (chi g)))
          map_add' := fun f h => by
            funext i
            exact map_add (A.ρ g) _ _
          map_smul' := fun r f => by
            funext i
            exact map_smul (A.ρ g) r _ }
      map_one' := by
        apply LinearMap.ext
        intro f
        funext i
        simp
      map_mul' := fun g h => by
        apply LinearMap.ext
        intro f
        funext i
        change A.ρ (g * h)
            (f (i + Multiplicative.toAdd (chi (g * h)))) =
          A.ρ g (A.ρ h
            (f ((i + Multiplicative.toAdd (chi g)) +
              Multiplicative.toAdd (chi h))))
        rw [map_mul A.ρ]
        change A.ρ g (A.ρ h
            (f (i + Multiplicative.toAdd (chi (g * h))))) = _
        rw [map_mul chi]
        change A.ρ g (A.ρ h
            (f (i + (Multiplicative.toAdd (chi g) +
              Multiplicative.toAdd (chi h))))) = _
        rw [add_assoc] }

@[simp]
theorem cyclicPermutation_rho_apply
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell)) (A : Rep.{uA} k G)
    (g : G) (f : ZMod ell → A) (i : ZMod ell) :
    (cyclicPermutation ell chi A).ρ g f i =
      A.ρ g (f (i + Multiplicative.toAdd (chi g))) :=
  rfl

/-- Let k be a commutative ring, G a group, A a k-linear
G-representation and χ:G→Multiplicative(ZMod ℓ) a character.
Write χ_add(g) for its additive ZMod ℓ value and
Pχ(A)=ZMod ℓ→A, with (g•p)(i)=g•p(i+χ_add(g)).
The equivariant diagonal map δ:A→Pχ(A) sends a to the constant
function i↦a. -/
noncomputable def cyclicPermutationDiagonal
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell)) (A : Rep.{uA} k G) :
    A ⟶ cyclicPermutation ell chi A := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun a _ => a
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro a
  funext i
  rfl

@[simp]
theorem cyclicPermutationDiagonal_apply
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell)) (A : Rep.{uA} k G)
    (a : A) (i : ZMod ell) :
    (cyclicPermutationDiagonal ell chi A).hom a i = a :=
  rfl

/-- Let k be a commutative ring, G a group, A a k-linear
G-representation and χ:G→Multiplicative(ZMod ℓ) a character.
Write χ_add(g) for its additive ZMod ℓ value and
Pχ(A)=ZMod ℓ→A, with (g•p)(i)=g•p(i+χ_add(g)).
For ℓ≠0, the equivariant augmentation is
ε:Pχ(A)→A, p↦∑_(i:ZMod ℓ)p(i). -/
noncomputable def cyclicPermutationAugmentation
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell)) (A : Rep.{uA} k G) :
    cyclicPermutation ell chi A ⟶ A := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        { toFun := fun f => ∑ i : ZMod ell, f i
          map_add' := fun f h => by
            simp only [Pi.add_apply, Finset.sum_add_distrib]
          map_smul' := fun r f => by
            simp only [Pi.smul_apply, Finset.smul_sum,
              RingHom.id_apply] }
      isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro f
  change (∑ i : ZMod ell,
      A.ρ g (f (i + Multiplicative.toAdd (chi g)))) =
    A.ρ g (∑ i : ZMod ell, f i)
  rw [← map_sum]
  exact congrArg (A.ρ g)
    (Equiv.sum_comp
      (Equiv.addRight (Multiplicative.toAdd (chi g))) f)

@[simp]
theorem cyclicPermutationAugmentation_apply
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell)) (A : Rep.{uA} k G)
    (f : ZMod ell → A) :
    (cyclicPermutationAugmentation ell chi A).hom f =
      ∑ i : ZMod ell, f i :=
  rfl

/-- Let k be a commutative ring, G a group, A a k-linear
G-representation and χ:G→Multiplicative(ZMod ℓ) a character.
Write χ_add(g) for its additive ZMod ℓ value and
Pχ(A)=ZMod ℓ→A, with (g•p)(i)=g•p(i+χ_add(g)).
For ℓ≠0, summation after constant inclusion satisfies
ε∘δ=ℓ•id_A. -/
theorem cyclicPermutationDiagonal_comp_augmentation
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell)) (A : Rep.{uA} k G) :
    cyclicPermutationDiagonal ell chi A ≫
        cyclicPermutationAugmentation ell chi A =
      ell • 𝟙 A := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change (∑ _i : ZMod ell, a) = ell • a
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]

/-- Every i∈ZMod 2 is either 0 or 1. -/
theorem zmodTwo_eq_zero_or_one (i : ZMod 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- For any additive commutative monoid M and f:ZMod 2→M,
∑_i f(i)=f(0)+f(1). -/
theorem sum_zmodTwo {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    (∑ i : ZMod 2, f i) = f 0 + f 1 := by
  calc
    (∑ i : ZMod 2, f i) =
        ∑ i : Fin 2, f (ZMod.finEquiv 2 i) :=
      (Equiv.sum_comp (ZMod.finEquiv 2).toEquiv f).symm
    _ = f 0 + f 1 := by
      rw [Fin.sum_univ_two]
      rfl

/-- Let G be a group, χ:G→Multiplicative(ZMod 2) a character,
and A a ZMod 2-linear G-representation. The diagonal δ:A→Pχ(A)
is constant inclusion and ε:Pχ(A)→A is summation of the two coordinates.
The diagonal δ is injective on underlying coefficient modules. -/
theorem cyclicPermutationDiagonal_two_injective
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    Function.Injective (cyclicPermutationDiagonal 2 chi A).hom := by
  intro a b h
  change (fun _ : ZMod 2 => a) = (fun _ : ZMod 2 => b) at h
  exact congrFun h 0

/-- Let G be a group, χ:G→Multiplicative(ZMod 2) a character,
and A a ZMod 2-linear G-representation. The diagonal δ:A→Pχ(A)
is constant inclusion and ε:Pχ(A)→A is summation of the two coordinates.
The augmentation ε is surjective on underlying modules,
with a preimage obtained by placing a in one coordinate. -/
theorem cyclicPermutationAugmentation_two_surjective
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    Function.Surjective (cyclicPermutationAugmentation 2 chi A).hom := by
  intro a
  let f : ZMod 2 → A := Pi.single 0 a
  refine ⟨f, ?_⟩
  change (∑ i : ZMod 2, f i) = a
  simp [f]

/-- Let G be a group, χ:G→Multiplicative(ZMod 2) a character,
and A a ZMod 2-linear G-representation. The diagonal δ:A→Pχ(A)
is constant inclusion and ε:Pχ(A)→A is summation of the two coordinates.
The sequence A→Pχ(A)→A is exact at Pχ(A):
the kernel of coordinate sum is the constant diagonal image. -/
theorem cyclicPermutation_two_exact
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    Function.Exact (cyclicPermutationDiagonal 2 chi A).hom
      (cyclicPermutationAugmentation 2 chi A).hom := by
  intro f
  constructor
  · intro hsum
    refine ⟨f 0, ?_⟩
    change (fun _i : ZMod 2 => f 0) = f
    funext i
    rcases zmodTwo_eq_zero_or_one i with rfl | rfl
    · rfl
    · have hpair : f 0 + f 1 = 0 := by
        rw [cyclicPermutationAugmentation_apply] at hsum
        simpa only [sum_zmodTwo] using hsum
      have hself : f 0 + f 0 = 0 := by
        calc
          f 0 + f 0 = (2 : ℕ) • f 0 := (two_nsmul _).symm
          _ = (2 : ZMod 2) • f 0 :=
            (Nat.cast_smul_eq_nsmul (ZMod 2) 2 (f 0)).symm
          _ = 0 := by
            rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
      exact (add_left_cancel (hpair.trans hself.symm)).symm
  · rintro ⟨a, ha⟩
    rw [← ha]
    change (∑ _i : ZMod 2, a) = 0
    calc
      (∑ _i : ZMod 2, a) = a + a := sum_zmodTwo _
      _ = (2 : ℕ) • a := (two_nsmul _).symm
      _ = (2 : ZMod 2) • a :=
        (Nat.cast_smul_eq_nsmul (ZMod 2) 2 a).symm
      _ = 0 := by
        rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- Let G be a group, χ:G→Multiplicative(ZMod 2) a character,
and A a ZMod 2-linear G-representation. The diagonal δ:A→Pχ(A)
is constant inclusion and ε:Pχ(A)→A is summation of the two coordinates.
Since ε∘δ=2•id_A=0, the diagonal and augmentation form
this short complex of ZMod 2-representations. -/
noncomputable def cyclicPermutationTwoShortComplex
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    ShortComplex (Rep.{uA} (ZMod 2) G) :=
  ShortComplex.mk
    (cyclicPermutationDiagonal 2 chi A)
    (cyclicPermutationAugmentation 2 chi A) (by
      rw [cyclicPermutationDiagonal_comp_augmentation]
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      change (2 : ℕ) • a = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      change (2 : ZMod 2) • a = 0
      rw [show (2 : ZMod 2) = 0 by decide, zero_smul])

@[simp]
theorem cyclicPermutationTwoShortComplex_f
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    (cyclicPermutationTwoShortComplex chi A).f =
      cyclicPermutationDiagonal 2 chi A :=
  rfl

@[simp]
theorem cyclicPermutationTwoShortComplex_g
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    (cyclicPermutationTwoShortComplex chi A).g =
      cyclicPermutationAugmentation 2 chi A :=
  rfl

/-- Let G be a group, χ:G→Multiplicative(ZMod 2) a character,
and A a ZMod 2-linear G-representation. The diagonal δ:A→Pχ(A)
is constant inclusion and ε:Pχ(A)→A is summation of the two coordinates.
The diagonal/augmentation short complex is short exact in
the representation category. -/
theorem cyclicPermutationTwoShortComplex_shortExact
    (chi : G →* Multiplicative (ZMod 2))
    (A : Rep.{uA} (ZMod 2) G) :
    (cyclicPermutationTwoShortComplex chi A).ShortExact := by
  let S := cyclicPermutationTwoShortComplex chi A
  let F := forget₂ (Rep.{uA} (ZMod 2) G) (ModuleCat.{uA} (ZMod 2))
  have hExact : S.Exact := by
    apply F.reflects_exact_of_faithful
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    intro x
    exact cyclicPermutation_two_exact chi A x
  let _ : Mono S.f := by
    dsimp only [S, cyclicPermutationTwoShortComplex]
    exact (Rep.mono_iff_injective _).2
      (cyclicPermutationDiagonal_two_injective chi A)
  let _ : Epi S.g := by
    dsimp only [S, cyclicPermutationTwoShortComplex]
    exact (Rep.epi_iff_surjective _).2
      (cyclicPermutationAugmentation_two_surjective chi A)
  exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance

end Rep
