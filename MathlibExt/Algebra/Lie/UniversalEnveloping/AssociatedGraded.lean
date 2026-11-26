/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Filtration
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import MathlibExt.RingTheory.FilteredAlgebra.AssociatedGradedMap
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# The associated graded of a universal enveloping algebra

Let R be a commutative ring, L an R-Lie algebra, and U=U_R(L). Its degree filtration D_n is
spanned by products of at most n Lie generators. The direct sum of the quotient layers
D_n/D_{<n}, with multiplication induced from U, is the intrinsic associated graded algebra.
Commutators lower degree, so this algebra is commutative without a freeness or projectivity
hypothesis on L.

A Lie map induces a graded R-algebra map. The linear map x ↦ the degree-one symbol of ι(x)
extends to an R-algebra map Sym_R(L) → gr(U), natural for Lie maps between independently sized
Lie algebras.
-/

@[expose] public section

noncomputable section

universe u v v' v''

namespace UniversalEnvelopingAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

instance degreeFiltration_gradedMonoid : SetLike.GradedMonoid (degreeFiltration R L) where
  one_mem := one_mem_degreeFiltration R L 0
  mul_mem := fun _ _ _ _ ha hb => mul_mem_degreeFiltration R L ha hb

instance degreeFiltration_isRingFiltration :
    IsRingFiltration (degreeFiltration R L) (FilteredAlgebra.lower (degreeFiltration R L)) where
  __ := FilteredAlgebra.isFiltration_lower (degreeFiltration R L) (degreeFiltration_mono R L)
  __ := degreeFiltration_gradedMonoid R L

/-- For a commutative ring R and an R-Lie algebra L, let D_n be the degree filtration of U_R(L).
Define gr(U_R(L)) as the finite-support direct sum of the quotient layers D_n/D_{<n}. Here
D_{<0}=0 and, for n>0, D_{<n} is the preceding degree stage inside D_n. Multiplication sends
degree-n and degree-m classes to the degree-(n+m) class of their enveloping product, and the
scalar map lies in degree zero. -/
abbrev AssociatedGraded := FilteredAlgebra.AssociatedGraded (degreeFiltration R L)

/-- Let R be a commutative ring, L an R-Lie algebra, x ∈ L, and ys a finite list of elements of L.
Write w(ys) for the product of their images under ι : L → U_R(L), with the empty product equal
to 1. Then ι(x)w(ys) − w(ys)ι(x) belongs to D_{length(ys)}. Thus commuting one generator past
a word lowers the product's filtration degree by one. -/
theorem ι_word_commutator_mem_degreeFiltration (x : L) (ys : List L) :
    ι R x * word R L ys - word R L ys * ι R x ∈ degreeFiltration R L ys.length := by
  induction ys with
  | nil =>
      rw [word_nil, mul_one, one_mul, sub_self]
      exact (degreeFiltration R L 0).zero_mem
  | cons y ys ih =>
      have hleft : (ι R x * ι R y - ι R y * ι R x) * word R L ys ∈
          degreeFiltration R L (1 + ys.length) :=
        mul_mem_degreeFiltration R L (ι_commutator_mem_degreeFiltration R L x y)
          (word_mem_degreeFiltration R L ys ys.length le_rfl)
      have hright : ι R y * (ι R x * word R L ys - word R L ys * ι R x) ∈
          degreeFiltration R L (1 + ys.length) :=
        mul_mem_degreeFiltration R L (ι_mem_degreeFiltration R L y) ih
      have heq : ι R x * (ι R y * word R L ys) - (ι R y * word R L ys) * ι R x =
          (ι R x * ι R y - ι R y * ι R x) * word R L ys +
            ι R y * (ι R x * word R L ys - word R L ys * ι R x) := by
        noncomm_ring
      rw [word_cons, heq]
      exact degreeFiltration_mono R L (by simp only [List.length_cons]; omega)
        ((degreeFiltration R L (1 + ys.length)).add_mem hleft hright)

/-- For a commutative ring R, an R-Lie algebra L, and lists xs,ys of Lie elements, let w(xs),w(ys)
be their ordered enveloping products. The commutator w(xs)w(ys) − w(ys)w(xs) lies in
D_{length(xs)+length(ys)−1}. The subtraction in the stage index is natural-number subtraction.
This statement includes empty words, whose commutators vanish. -/
theorem word_commutator_mem_degreeFiltration (xs ys : List L) :
    word R L xs * word R L ys - word R L ys * word R L xs ∈
      degreeFiltration R L (xs.length + ys.length - 1) := by
  induction xs generalizing ys with
  | nil =>
      rw [word_nil, one_mul, mul_one, sub_self]
      exact (degreeFiltration R L (0 + ys.length - 1)).zero_mem
  | cons x xs ih =>
      cases ys with
      | nil =>
          rw [word_nil, mul_one, one_mul, sub_self]
          exact (degreeFiltration R L ((x :: xs).length + 0 - 1)).zero_mem
      | cons y ys =>
          have hleft := mul_mem_degreeFiltration R L (ι_mem_degreeFiltration R L x)
            (ih (y :: ys))
          have hright := mul_mem_degreeFiltration R L
            (ι_word_commutator_mem_degreeFiltration R L x (y :: ys))
            (word_mem_degreeFiltration R L xs xs.length le_rfl)
          have hleft' : ι R x *
              (word R L xs * word R L (y :: ys) - word R L (y :: ys) * word R L xs) ∈
              degreeFiltration R L ((x :: xs).length + (y :: ys).length - 1) :=
            degreeFiltration_mono R L (by simp only [List.length_cons]; omega) hleft
          have hright' :
              (ι R x * word R L (y :: ys) - word R L (y :: ys) * ι R x) * word R L xs ∈
              degreeFiltration R L ((x :: xs).length + (y :: ys).length - 1) :=
            degreeFiltration_mono R L (by simp only [List.length_cons]; omega) hright
          have heq : (ι R x * word R L xs) * word R L (y :: ys) -
              word R L (y :: ys) * (ι R x * word R L xs) =
                ι R x * (word R L xs * word R L (y :: ys) -
                  word R L (y :: ys) * word R L xs) +
                (ι R x * word R L (y :: ys) - word R L (y :: ys) * ι R x) * word R L xs := by
            noncomm_ring
          rw [word_cons, heq]
          exact (degreeFiltration R L ((x :: xs).length + (y :: ys).length - 1)).add_mem
            hleft' hright'

/-- Let R be a commutative ring, L an R-Lie algebra, a ∈ D_n and b ∈ D_m in U_R(L), with n,m ∈ ℕ.
Then ab−ba belongs to D_{<n+m}, the lower submodule used to define the degree-(n+m) quotient.
For n+m>0 this is the preceding degree stage, while at n+m=0 it is zero. Consequently the
symbols of a and b commute in the associated graded algebra. -/
theorem commutator_mem_degreeFiltration_lower {n m : ℕ}
    {a b : UniversalEnvelopingAlgebra R L}
    (ha : a ∈ degreeFiltration R L n) (hb : b ∈ degreeFiltration R L m) :
    a * b - b * a ∈ FilteredAlgebra.lower (degreeFiltration R L) (n + m) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨xs, hxs, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨ys, hys, rfl⟩ := hb
          by_cases hnm : n + m = 0
          · have hn : n = 0 := by omega
            have hm : m = 0 := by omega
            have hxnil : xs = [] := List.length_eq_zero_iff.mp
              (Nat.le_zero.mp (by simpa only [hn] using hxs))
            have hynil : ys = [] := List.length_eq_zero_iff.mp
              (Nat.le_zero.mp (by simpa only [hm] using hys))
            rw [hxnil, hynil, word_nil, sub_self]
            exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).zero_mem
          · have hword := word_commutator_mem_degreeFiltration R L xs ys
            have hbound : xs.length + ys.length - 1 ≤ n + m - 1 :=
              Nat.sub_le_sub_right (Nat.add_le_add hxs hys) 1
            have htarget := degreeFiltration_mono R L hbound hword
            cases hdegree : n + m with
            | zero => exact (hnm hdegree).elim
            | succ k => simpa [hdegree, FilteredAlgebra.lower] using htarget
      | zero =>
          rw [mul_zero, zero_mul, sub_self]
          exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).zero_mem
      | add b c hb hc ihb ihc =>
          have heq : word R L xs * (b + c) - (b + c) * word R L xs =
              (word R L xs * b - b * word R L xs) +
                (word R L xs * c - c * word R L xs) := by noncomm_ring
          rw [heq]
          exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).add_mem ihb ihc
      | smul r b hb ih =>
          rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
          exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).smul_mem r ih
  | zero =>
      rw [zero_mul, mul_zero, sub_self]
      exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).zero_mem
  | add a c ha hc iha ihc =>
      have heq : (a + c) * b - b * (a + c) = (a * b - b * a) + (c * b - b * c) := by
        noncomm_ring
      rw [heq]
      exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).add_mem iha ihc
  | smul r a ha ih =>
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
      exact (FilteredAlgebra.lower (degreeFiltration R L) (n + m)).smul_mem r ih

/-- For any R-Lie algebra L over a commutative ring R, the intrinsic associated graded ring
gr(U_R(L)) is a commutative ring. Its multiplication is induced by enveloping products on
quotient layers, and commutativity follows because [D_n,D_m] ⊆ D_{<n+m}. This requires neither
an ordered basis nor freeness or projectivity of L. -/
instance associatedGradedCommRing : CommRing (AssociatedGraded R L) where
  __ := (inferInstance : Ring (AssociatedGraded R L))
  mul_comm := FilteredAlgebra.mul_comm_of_commutator_mem (degreeFiltration R L)
    (fun n m u v => commutator_mem_degreeFiltration_lower R L u.property v.property)

/-- Let R be a commutative ring, L an R-Lie algebra, and n ∈ ℕ. The R-linear symbol map D_n →
gr(U_R(L)) first takes the class modulo D_{<n}, then inserts that class into degree n of the
quotient direct sum. Thus changing a representative by an element of D_{<n} leaves its
degree-n symbol unchanged. -/
def associatedGradedSymbol (n : ℕ) : degreeFiltration R L n →ₗ[R] AssociatedGraded R L :=
  FilteredAlgebra.symbol (degreeFiltration R L) n

theorem associatedGradedSymbol_mul (n m : ℕ)
    (a : degreeFiltration R L n) (b : degreeFiltration R L m) :
    associatedGradedSymbol R L n a * associatedGradedSymbol R L m b =
      associatedGradedSymbol R L (n + m)
        ⟨a.val * b.val, mul_mem_degreeFiltration R L a.property b.property⟩ :=
  FilteredAlgebra.symbol_mul (degreeFiltration R L) n m a b

theorem associatedGradedSymbol_one :
    associatedGradedSymbol R L 0 ⟨(1 : UniversalEnvelopingAlgebra R L),
      one_mem_degreeFiltration R L 0⟩ = 1 :=
  FilteredAlgebra.symbol_one (degreeFiltration R L)

theorem associatedGradedSymbol_algebraMap (r : R) :
    associatedGradedSymbol R L 0 ⟨algebraMap R (UniversalEnvelopingAlgebra R L) r,
      algebraMap_mem_degreeFiltration R L 0 r⟩ = algebraMap R (AssociatedGraded R L) r :=
  FilteredAlgebra.symbol_algebraMap (degreeFiltration R L) r

variable {L} {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

/-- Let R be a commutative ring and f : L →ₗ⁅R⁆ L′ a Lie map between R-Lie algebras with
independent carrier universes. For a list xs of elements of L, the canonical algebra map
U_R(f) sends w_L(xs) to w_L′(xs.map(f)). The words are ordered products of the Lie-generator
images, with the empty word equal to the unit. -/
theorem map_word (f : L →ₗ⁅R⁆ L') (xs : List L) :
    map R f (word R L xs) = word R L' (xs.map f) := by
  induction xs with
  | nil => rw [word_nil, List.map_nil, word_nil, map_one]
  | cons x xs ih =>
      rw [word_cons, map_mul, map_ι, ih, List.map_cons, word_cons]

/-- Let R be a commutative ring, f : L →ₗ⁅R⁆ L′ a Lie map, n ∈ ℕ, and a ∈ D_n(U_R(L)). Then
U_R(f)(a) belongs to D_n(U_R(L′)). The degree filtration is the R-span of words of length at
most n, and the map sends each such word to the word in its image generators. No condition on
f beyond being an R-Lie map is required. -/
theorem map_mem_degreeFiltration (f : L →ₗ⁅R⁆ L') (n : ℕ)
    {a : UniversalEnvelopingAlgebra R L} (ha : a ∈ degreeFiltration R L n) :
    map R f a ∈ degreeFiltration R L' n := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨xs, hxs, rfl⟩ := ha
      rw [map_word]
      exact word_mem_degreeFiltration R L' (xs.map f) n (by
        simpa only [List.length_map] using hxs)
  | zero => rw [map_zero]; exact (degreeFiltration R L' n).zero_mem
  | add a b ha hb iha ihb =>
      rw [map_add]
      exact (degreeFiltration R L' n).add_mem iha ihb
  | smul r a ha ih =>
      rw [map_smul]
      exact (degreeFiltration R L' n).smul_mem r ih

/-- Let R be a commutative ring and f : L →ₗ⁅R⁆ L′ a Lie map. The filtration-preserving enveloping
map U_R(f) induces an R-algebra map gr(U_R(L)) → gr(U_R(L′)). On the degree-n class of a ∈ D_n
it takes the symbol of a to the degree-n symbol of U_R(f)(a). The Lie carriers may lie in
independent universes, and no basis hypothesis is imposed. -/
def associatedGradedMap (f : L →ₗ⁅R⁆ L') : AssociatedGraded R L →ₐ[R] AssociatedGraded R L' :=
  FilteredAlgebra.map (degreeFiltration R L) (degreeFiltration R L') (map R f)
    (fun n _ ha => map_mem_degreeFiltration R f n ha)

@[simp]
theorem associatedGradedMap_symbol (f : L →ₗ⁅R⁆ L') (n : ℕ)
    (a : degreeFiltration R L n) :
    associatedGradedMap R f (associatedGradedSymbol R L n a) =
      associatedGradedSymbol R L' n
        ⟨map R f a.val, map_mem_degreeFiltration R f n a.property⟩ :=
  FilteredAlgebra.map_symbol (degreeFiltration R L) (degreeFiltration R L') (map R f)
    (fun n _ ha => map_mem_degreeFiltration R f n ha) n a

@[simp]
theorem associatedGradedMap_id :
    associatedGradedMap R (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R (AssociatedGraded R L) := by
  apply DFunLike.ext
  intro x
  refine FilteredAlgebra.symbol_induction (degreeFiltration R L) ?_ ?_ ?_ x
  · simp only [map_zero]
  · intro n u
    have h := associatedGradedMap_symbol R (LieHom.id : L →ₗ⁅R⁆ L) n u
    have hu : (⟨map R (LieHom.id : L →ₗ⁅R⁆ L) u.val,
        map_mem_degreeFiltration R (LieHom.id : L →ₗ⁅R⁆ L) n u.property⟩ :
          degreeFiltration R L n) = u := by
      apply Subtype.ext
      exact congrArg (fun f : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L =>
        f u.val) (UniversalEnvelopingAlgebra.map_id (L := L) R)
    exact h.trans (congrArg (associatedGradedSymbol R L n) hu)
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem associatedGradedMap_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    associatedGradedMap R (g.comp f) =
      (associatedGradedMap R g).comp (associatedGradedMap R f) := by
  apply DFunLike.ext
  intro x
  refine FilteredAlgebra.symbol_induction (degreeFiltration R L) ?_ ?_ ?_ x
  · simp only [map_zero, AlgHom.comp_apply]
  · intro n u
    have hLeft := associatedGradedMap_symbol R (g.comp f) n u
    have hFirst := associatedGradedMap_symbol R f n u
    let fu : degreeFiltration R L' n := ⟨map R f u.val, map_mem_degreeFiltration R f n u.property⟩
    have hSecond := associatedGradedMap_symbol R g n fu
    have hEq : (⟨map R (g.comp f) u.val, map_mem_degreeFiltration R (g.comp f) n u.property⟩ :
        degreeFiltration R L'' n) =
        ⟨map R g fu.val, map_mem_degreeFiltration R g n fu.property⟩ := by
      apply Subtype.ext
      exact congrArg (fun h : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L'' =>
        h u.val) (UniversalEnvelopingAlgebra.map_comp R f g)
    exact hLeft.trans ((congrArg (associatedGradedSymbol R L'' n) hEq).trans
      (hSecond.symm.trans (congrArg (associatedGradedMap R g) hFirst.symm)))
  · intro x y hx hy
    simp only [map_add, AlgHom.comp_apply, hx, hy]

variable (L)

/-- For an R-Lie algebra L over a commutative ring R, define the R-linear map L → gr(U_R(L)) by x
↦ the degree-one symbol of ι(x). The generator ι(x) belongs to D_1, so its class modulo the
degree-zero stage is inserted in homogeneous degree one of the intrinsic associated graded
algebra. -/
def associatedGradedGeneratorSymbol : L →ₗ[R] AssociatedGraded R L :=
  (associatedGradedSymbol R L 1).comp
    ((show L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L from ι R).toLinearMap.codRestrict (degreeFiltration R L 1)
      (ι_mem_degreeFiltration R L))

@[simp]
theorem associatedGradedGeneratorSymbol_apply (x : L) :
    associatedGradedGeneratorSymbol R L x =
      associatedGradedSymbol R L 1 ⟨ι R x, ι_mem_degreeFiltration R L x⟩ := rfl

/-- For an R-Lie algebra L over a commutative ring R, the R-linear generator-symbol map x ↦
symbol_1(ι(x)) extends uniquely to an R-algebra map Sym_R(L) → gr(U_R(L)). This uses
commutativity of the intrinsic associated graded enveloping algebra. The construction applies
to arbitrary L; it does not assume that this comparison is invertible. -/
def symmetricComparison : SymmetricAlgebra R L →ₐ[R] AssociatedGraded R L :=
  SymmetricAlgebra.lift (associatedGradedGeneratorSymbol R L)

@[simp]
theorem symmetricComparison_ι (x : L) :
    symmetricComparison R L (SymmetricAlgebra.ι R L x) =
      associatedGradedGeneratorSymbol R L x :=
  SymmetricAlgebra.lift_ι_apply (associatedGradedGeneratorSymbol R L) x

variable {L}

theorem associatedGradedMap_generatorSymbol (f : L →ₗ⁅R⁆ L') (x : L) :
    associatedGradedMap R f (associatedGradedGeneratorSymbol R L x) =
      associatedGradedGeneratorSymbol R L' (f x) := by
  rw [associatedGradedGeneratorSymbol_apply, associatedGradedMap_symbol,
    associatedGradedGeneratorSymbol_apply]
  apply congrArg (associatedGradedSymbol R L' 1)
  apply Subtype.ext
  exact map_ι R f x

/-- Let R be a commutative ring and f : L →ₗ⁅R⁆ L′ a Lie map. If c_L : Sym_R(L) → gr(U_R(L)) and
c_L′ are the generator-symbol comparisons, then gr(U_R(f)) ∘ c_L = c_L′ ∘ Sym_R(f). Here
Sym_R(f) sends the symmetric generator x to the generator f(x). This is an equality of
R-algebra maps, valid without free or projective hypotheses and with independent Lie carrier
universes. -/
theorem symmetricComparison_naturality (f : L →ₗ⁅R⁆ L') :
    (associatedGradedMap R f).comp (symmetricComparison R L) =
      (symmetricComparison R L').comp
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L').comp f.toLinearMap)) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change associatedGradedMap R f (symmetricComparison R L (SymmetricAlgebra.ι R L x)) =
    symmetricComparison R L'
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L').comp f.toLinearMap)
        (SymmetricAlgebra.ι R L x))
  rw [symmetricComparison_ι, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
    symmetricComparison_ι, associatedGradedMap_generatorSymbol]
  rfl

end UniversalEnvelopingAlgebra
