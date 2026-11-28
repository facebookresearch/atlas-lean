/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, @junekim623, Muse
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
/-!
# Integer-graded modules and degree-zero homogeneous fractions

Let R be a commutative ring with a natural-number grading R = ⊕ₙ𝒜_n. A graded module has an
integer-indexed decomposition M = ⊕ᵢM_i satisfying 𝒜_n·M_i ⊆ M_{i+n}. Degree-preserving
R-linear maps form a preadditive category, with a functor to the underlying module category.

For a submonoid S ⊆ R, the degree-zero homogeneous fraction module uses representatives m/s
with m ∈ M_n and s ∈ 𝒜_n ∩ S for n ∈ ℕ. Two representatives are equal when a multiplier from S
annihilates their cross-difference. The quotient is a module over the degree-zero homogeneous
localization ring, with the usual common-denominator addition and scalar multiplication.

The integer shift is M(n)_i = M_{i+n}. Extending the natural ring grading by zero in negative
degrees gives the graded regular module R, and multiplication by a homogeneous element of
degree m maps R(n) to R(n+m).

Historical formalization credit from the prior source: @junekim623, Muse.
-/

@[expose] public section
universe u
open CategoryTheory DirectSum
/-- Translation action of natural numbers on integer degrees.

The additive action is n +ᵥ z = z+n for n ∈ ℕ and z ∈ ℤ. -/
@[instance_reducible]
def addActionNatInt : AddAction Nat Int where
  vadd n z := z + (n : Int)
  zero_vadd z := by
    change z + ((0 : Nat) : Int) = z
    simp
  add_vadd m n z := by
    change z + ((m + n : Nat) : Int) = (z + (n : Int)) + (m : Int)
    calc z + ((m + n : Nat) : Int) = z + ((m : Int) + (n : Int)) := by rw [Nat.cast_add]
      _ = z + ((n : Int) + (m : Int)) := by rw [add_comm (m : Int) n]
      _ = (z + (n : Int)) + (m : Int) := by rw [add_assoc]

/-- Natural translation for integer-indexed module components.

The natural-number action on integer degrees uses n +ᵥ z = z+n. -/
local instance instAddActionNatInt : AddAction Nat Int := addActionNatInt

/-- Graded modules over a naturally graded commutative ring.

For a commutative ring R with ℕ-grading 𝒜, an object is an R-module M with an integer-indexed
direct-sum decomposition and scalar compatibility 𝒜_n·M_i ⊆ M_{i+n}. -/
structure GradedModuleCat {R : Type u} [CommRing R] {σS : Type*} [SetLike σS R]
    [AddSubgroupClass σS R] (𝒜 : ℕ → σS) [GradedRing 𝒜] where
  /-- The underlying carrier of a graded module.

This is the module carrier in the stated universe of the coefficient ring R. -/
  carrier : Type u
/-- The additive group structure of a graded module.

The carrier of the graded module is an additive commutative group. -/
  addCommGroup : AddCommGroup carrier
/-- The scalar module structure of a graded module.

The carrier is an R-module, compatible with its additive group structure. -/
  module : Module R carrier
  /-- The integer-indexed homogeneous components.

For i ∈ ℤ, grade i is the additive subgroup M_i of elements homogeneous of degree i. -/
  grade : ℤ → AddSubgroup carrier
  /-- The direct-sum decomposition by homogeneous components.

Every element of M decomposes uniquely as a finite sum of components in the M_i, giving M ≅
⊕_{i∈ℤ} M_i as additive groups. -/
  decomposition : DirectSum.Decomposition grade
/-- Compatibility of scalar multiplication with the gradings.

A homogeneous scalar in 𝒜_n sends M_i into M_{i+n}, with n ∈ ℕ and i ∈ ℤ. -/
  gradedSMul : SetLike.GradedSMul 𝒜 grade

attribute [instance] GradedModuleCat.addCommGroup GradedModuleCat.module

namespace GradedModuleCat

/-- Integer degree translation in the graded module category.

Natural degrees act on integer module degrees by n +ᵥ i = i+n. -/
scoped instance instAddActionNatIntScoped : AddAction Nat Int := addActionNatInt

variable {R : Type u} [CommRing R] {σS : Type*} [SetLike σS R] [AddSubgroupClass σS R]
  {𝒜 : ℕ → σS} [GradedRing 𝒜]

/-- The additive subgroup of degree-preserving linear maps.

Inside Hom_R(M,N), take the maps f with f(M_i) ⊆ N_i for every i ∈ ℤ. They are closed under
zero, addition and negation. -/
def homSubgroup (M N : GradedModuleCat (𝒜 := 𝒜)) :
    AddSubgroup (M.carrier →ₗ[R] N.carrier) where
  carrier := { f | ∀ (i : ℤ) (x : M.carrier), x ∈ M.grade i → f x ∈ N.grade i }
  zero_mem' := by
    intro i x hx
    exact (N.grade i).zero_mem
  add_mem' := by
    intro f g hf hg i x hx
    exact (N.grade i).add_mem (hf i x hx) (hg i x hx)
  neg_mem' := by
    intro f hf i x hx
    exact (N.grade i).neg_mem (hf i x hx)

/-- The morphism type of graded modules.

A morphism is an R-linear map preserving every integer homogeneous component, regarded as an
element of homSubgroup M N. -/
abbrev HomStruct (M N : GradedModuleCat (𝒜 := 𝒜)) := ↥(homSubgroup (𝒜 := 𝒜) M N)

namespace HomStruct

variable {M N : GradedModuleCat (𝒜 := 𝒜)}

/-- The linear map underlying a graded morphism.

Forget the degree-preservation proof of f to obtain its R-linear map M → N. -/
def toLinearMap (f : HomStruct (𝒜 := 𝒜) M N) : M.carrier →ₗ[R] N.carrier := f.val

/-- A graded morphism preserves each homogeneous degree.

If x ∈ M_i, then the underlying linear map of f sends x into N_i. -/
theorem preserves (f : HomStruct (𝒜 := 𝒜) M N) (i : ℤ) (x : M.carrier)
    (hx : x ∈ M.grade i) : f.val x ∈ N.grade i :=
  f.property i x hx

/-- Extensionality of graded morphisms.

Two graded morphisms are equal when their underlying R-linear maps are equal. -/
@[ext]
theorem ext {f g : HomStruct (𝒜 := 𝒜) M N} (h : f.val = g.val) : f = g :=
  Subtype.ext h

end HomStruct

instance : CategoryTheory.Category (GradedModuleCat (𝒜 := 𝒜)) where
  Hom M N := HomStruct M N
  id M := ⟨LinearMap.id, fun i x hx => hx⟩
  comp {X Y Z} f g :=
    ⟨g.val.comp f.val, fun i x hx => g.property i _ (f.property i x hx)⟩
  id_comp := by
    intro X Y f
    apply HomStruct.ext
    rfl
  comp_id := by
    intro X Y f
    apply HomStruct.ext
    rfl
  assoc := by
    intro W X Y Z f g h
    apply HomStruct.ext
    rfl

/-- The additive group of graded morphisms.

The degree-preserving morphisms M → N form an additive commutative group by their subgroup
structure inside the linear maps. -/
noncomputable instance instAddCommGroupHomStruct {M N : GradedModuleCat (𝒜 := 𝒜)} :
    AddCommGroup (HomStruct (𝒜 := 𝒜) M N) :=
  inferInstance

/-- The preadditive structure of the graded module category.

Composition of degree-preserving R-linear maps is additive in each variable, so the graded
module category is preadditive. -/
noncomputable instance instPreadditive : CategoryTheory.Preadditive (GradedModuleCat (𝒜 := 𝒜)) where
  homGroup M N := inferInstanceAs (AddCommGroup (HomStruct M N))
  add_comp := by
    intros P Q R f f' g
    apply HomStruct.ext
    change g.val.comp (f.val + f'.val) = g.val.comp f.val + g.val.comp f'.val
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
  comp_add := by
    intros P Q R f g g'
    apply HomStruct.ext
    change (g.val + g'.val).comp f.val = g.val.comp f.val + g'.val.comp f.val
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply]

/-- The functor forgetting the module grading.

Send a graded module to its underlying R-module and a graded morphism to its underlying
R-linear map. -/
noncomputable def forget : GradedModuleCat (𝒜 := 𝒜) ⥤ ModuleCat R where
  obj M :=
    letI := M.addCommGroup
    letI := M.module
    ModuleCat.of R M.carrier
  map {M N} f := ModuleCat.ofHom f.val
  map_id M := by
    ext
    rfl
  map_comp {X Y Z} f g := by
    ext
    rfl

/-!
# Degree-zero localization at a multiplicative submonoid

Represent a fraction by m ∈ M_n and s ∈ 𝒜_n ∩ S at a common nonnegative degree. The equality
relation is ∃t ∈ S, t·(s′·m − s·m′) = 0. Addition and the action of the homogeneous scalar
localization descend to these classes.
-/

/-- Homogeneous module fractions of degree zero.

For a submonoid S ⊆ R, a representative consists of m ∈ M_n and s ∈ 𝒜_n ∩ S for a common n ∈
ℕ, representing the degree-zero fraction m/s. -/
structure NumDenSameDegModuleAtPrime {R : Type u} [CommRing R]
    {σS : Type*} [SetLike σS R] [AddSubgroupClass σS R]
    {𝒜 : ℕ → σS} [GradedRing 𝒜]
    (M : GradedModuleCat (𝒜 := 𝒜)) (S : Submonoid R) where
  /-- The common nonnegative degree of a fraction representative.

This n ∈ ℕ is the homogeneous degree of both the module numerator and ring denominator. -/
  deg : ℕ
  /-- The module numerator of a homogeneous fraction.

The numerator is an element m of the underlying module carrier. -/
  m : M.carrier
/-- The homogeneous-degree condition on the fraction numerator.

The numerator m belongs to M_n, with n coerced from ℕ to the integer module grading. -/
  m_mem : m ∈ M.grade deg
  /-- The ring denominator of a homogeneous module fraction.

The denominator is the ring element s used in the representative m/s. -/
  s : R
/-- The homogeneous-degree condition on the fraction denominator.

The denominator s belongs to the ring component 𝒜_n at the common fraction degree. -/
  s_mem : s ∈ 𝒜 deg
/-- The localization condition on a fraction denominator.

The denominator s lies in the specified multiplicative submonoid S. -/
  s_in_S : s ∈ S

/-- The localization equivalence of homogeneous module fractions.

Representatives m/s and m′/s′ are equivalent when some t ∈ S satisfies t·(s′·m − s·m′) = 0.
This retains the annihilating multiplier needed for general modules. -/
def NumDenSameDegModuleAtPrime.setoid {R : Type u} [CommRing R]
    {σS : Type*} [SetLike σS R] [AddSubgroupClass σS R]
    {𝒜 : ℕ → σS} [GradedRing 𝒜]
    {M : GradedModuleCat (𝒜 := 𝒜)} {S : Submonoid R} :
    Setoid (NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S) where
  r x y := ∃ t ∈ S, t • ((y.s • x.m) - (x.s • y.m)) = 0
  iseqv := {
    refl := by intro x; exact ⟨1, Submonoid.one_mem _, by simp⟩
    symm := by
      intro x y ⟨t, ht, h⟩
      refine ⟨t, ht, ?_⟩
      have : (x.s • y.m - y.s • x.m) = -((y.s • x.m) - (x.s • y.m)) := by abel
      rw [this, smul_neg, h, neg_zero]
    trans := by
      intro x y z ⟨t1, ht1, h1⟩ ⟨t2, ht2, h2⟩
      refine ⟨t1 * t2 * y.s, Submonoid.mul_mem _ (Submonoid.mul_mem _ ht1 ht2) y.s_in_S, ?_⟩
      have heart : y.s • (z.s • x.m - x.s • z.m)
          = z.s • (y.s • x.m - x.s • y.m) + x.s • (z.s • y.m - y.s • z.m) := by
        have c1 : y.s • (z.s • x.m) = z.s • (y.s • x.m) := by
          rw [← mul_smul, ← mul_smul]; congr 1; ring
        have c2 : y.s • (x.s • z.m) = x.s • (y.s • z.m) := by
          rw [← mul_smul, ← mul_smul]; congr 1; ring
        have c3 : z.s • (x.s • y.m) = x.s • (z.s • y.m) := by
          rw [← mul_smul, ← mul_smul]; congr 1; ring
        simp only [smul_sub]
        rw [c1, c2, c3]
        abel
      have r1 : (t1 * t2) • (z.s • (y.s • x.m - x.s • y.m))
          = (t2 * z.s) • (t1 • (y.s • x.m - x.s • y.m)) := by
        rw [← mul_smul, ← mul_smul]; congr 1; ring
      have r2 : (t1 * t2) • (x.s • (z.s • y.m - y.s • z.m))
          = (t1 * x.s) • (t2 • (z.s • y.m - y.s • z.m)) := by
        rw [← mul_smul, ← mul_smul]; congr 1; ring
      calc (t1 * t2 * y.s) • (z.s • x.m - x.s • z.m)
          = (t1 * t2) • (y.s • (z.s • x.m - x.s • z.m)) := by rw [mul_smul]
        _ = (t1 * t2) • (z.s • (y.s • x.m - x.s • y.m)
            + x.s • (z.s • y.m - y.s • z.m)) := by rw [heart]
        _ = (t1 * t2) • (z.s • (y.s • x.m - x.s • y.m))
            + (t1 * t2) • (x.s • (z.s • y.m - y.s • z.m)) := by rw [smul_add]
        _ = (t2 * z.s) • (t1 • (y.s • x.m - x.s • y.m))
            + (t1 * x.s) • (t2 • (z.s • y.m - y.s • z.m)) := by rw [r1, r2]
        _ = 0 := by rw [h1, h2, smul_zero, smul_zero, add_zero]
  }

/-- The quotient of degree-zero homogeneous module fractions.

For any submonoid S, quotient the same-degree numerator–denominator representatives by
localization equivalence. -/
def AtPrimeModuleCarrier {R : Type u} [CommRing R]
    {σS : Type*} [SetLike σS R] [AddSubgroupClass σS R]
    {𝒜 : ℕ → σS} [GradedRing 𝒜]
    (M : GradedModuleCat (𝒜 := 𝒜)) (S : Submonoid R) : Type u :=
  Quotient (NumDenSameDegModuleAtPrime.setoid (M := M) (S := S))

namespace AtPrimeModuleCarrier

variable {R : Type u} [CommRing R] {σS : Type*} [SetLike σS R] [AddSubgroupClass σS R]
  {𝒜 : ℕ → σS} [GradedRing 𝒜] {M : GradedModuleCat (𝒜 := 𝒜)} {S : Submonoid R}

/-- The class of a homogeneous module fraction representative.

Send the data m ∈ M_n and s ∈ 𝒜_n ∩ S to its quotient class m/s. -/
noncomputable def mk (c : NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S) :
    AtPrimeModuleCarrier (𝒜 := 𝒜) M S := Quotient.mk _ c

/-- The zero homogeneous fraction.

Represent zero by 0/1 with common homogeneous degree zero. -/
noncomputable def zero : AtPrimeModuleCarrier (𝒜 := 𝒜) M S :=
  mk (M := M) (S := S) ⟨0, 0, (M.grade 0).zero_mem, 1, SetLike.one_mem_graded _,
    Submonoid.one_mem S⟩

/-- Addition of degree-zero homogeneous module fractions.

For representatives m/s and m′/s′, their sum is (s′·m + s·m′)/(ss′), with common degree equal
to the sum of the two original degrees. -/
noncomputable def add (x y : AtPrimeModuleCarrier (𝒜 := 𝒜) M S) :
    AtPrimeModuleCarrier (𝒜 := 𝒜) M S :=
  Quotient.liftOn₂ x y
    (fun (a : NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S)
         (b : NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S) =>
      mk (M := M) (S := S) ⟨a.deg + b.deg,
        b.s • a.m + a.s • b.m, by
          have := M.gradedSMul
          have h1 : b.s • a.m ∈ M.grade ((a.deg : ℤ) + (b.deg : ℤ)) :=
            SetLike.GradedSMul.smul_mem b.s_mem a.m_mem
          have h2 : a.s • b.m ∈ M.grade ((a.deg : ℤ) + (b.deg : ℤ)) := by
            have h := SetLike.GradedSMul.smul_mem a.s_mem b.m_mem
            rwa [show ((a.deg : ℕ) +ᵥ ((b.deg : ℕ) : ℤ))
              = ((b.deg : ℤ) + (a.deg : ℤ)) from rfl, add_comm] at h
          rw [Nat.cast_add]
          exact (M.grade _).add_mem h1 h2,
        a.s * b.s, SetLike.GradedMul.mul_mem a.s_mem b.s_mem,
        Submonoid.mul_mem _ a.s_in_S b.s_in_S⟩)
    (by
      intro a₁ b₁ a₂ b₂ h₁ h₂
      have h1w : ∃ t ∈ S, t • (a₂.s • a₁.m - a₁.s • a₂.m) = 0 := h₁
      have h2w : ∃ t ∈ S, t • (b₂.s • b₁.m - b₁.s • b₂.m) = 0 := h₂
      obtain ⟨t₁, ht₁, e₁⟩ := h1w
      obtain ⟨t₂, ht₂, e₂⟩ := h2w
      refine Quotient.sound ⟨t₁ * t₂, Submonoid.mul_mem _ ht₁ ht₂, ?_⟩
      have key : (a₂.s * b₂.s) • (b₁.s • a₁.m + a₁.s • b₁.m)
            - (a₁.s * b₁.s) • (b₂.s • a₂.m + a₂.s • b₂.m)
          = (b₁.s * b₂.s) • (a₂.s • a₁.m - a₁.s • a₂.m)
            + (a₁.s * a₂.s) • (b₂.s • b₁.m - b₁.s • b₂.m) := by module
      have z1 : (t₁ * t₂) • ((b₁.s * b₂.s) • (a₂.s • a₁.m - a₁.s • a₂.m)) = 0 := by
        have hj : (t₁ * t₂) • ((b₁.s * b₂.s) • (a₂.s • a₁.m - a₁.s • a₂.m))
            = (b₁.s * b₂.s) • (t₂ • (t₁ • (a₂.s • a₁.m - a₁.s • a₂.m))) := by
          module
        rw [hj, e₁, smul_zero, smul_zero]
      have z2 : (t₁ * t₂) • ((a₁.s * a₂.s) • (b₂.s • b₁.m - b₁.s • b₂.m)) = 0 := by
        have hj : (t₁ * t₂) • ((a₁.s * a₂.s) • (b₂.s • b₁.m - b₁.s • b₂.m))
            = (a₁.s * a₂.s) • (t₁ • (t₂ • (b₂.s • b₁.m - b₁.s • b₂.m))) := by
          module
        rw [hj, e₂, smul_zero, smul_zero]
      rw [key, smul_add, z1, z2, add_zero])

/-- Negation of a homogeneous module fraction.

The negative of m/s is represented by (−m)/s at the same homogeneous degree. -/
noncomputable def neg (x : AtPrimeModuleCarrier (𝒜 := 𝒜) M S) :
    AtPrimeModuleCarrier (𝒜 := 𝒜) M S :=
  Quotient.liftOn x
    (fun (a : NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S) =>
      mk (M := M) (S := S) ⟨a.deg, -a.m, (M.grade _).neg_mem a.m_mem, a.s, a.s_mem,
        a.s_in_S⟩)
    (by
      intro a b hab
      have hw : ∃ t ∈ S, t • (b.s • a.m - a.s • b.m) = 0 := hab
      obtain ⟨t, ht, e⟩ := hw
      refine Quotient.sound ⟨t, ht, ?_⟩
      have key : b.s • (-a.m) - a.s • (-b.m)
          = -((b.s • a.m - a.s • b.m) : M.carrier) := by module
      rw [key, smul_neg, e, neg_zero])

/-- The zero structure on homogeneous fraction classes.

The quotient carrier has zero given by the class 0/1. -/
noncomputable instance instZero : Zero (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  zero := zero (S := S)

/-- The addition structure on homogeneous fraction classes.

The quotient carrier uses the common-denominator addition formula for degree-zero module
fractions. -/
noncomputable instance instAdd : Add (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  add := add

/-- The negation structure on homogeneous fraction classes.

The additive inverse is induced by negating the numerator. -/
noncomputable instance instNeg : Neg (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  neg := neg

/-- Subtraction of homogeneous fraction classes.

Subtraction is addition with the negative numerator representative. -/
noncomputable instance instSub : Sub (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  sub x y := x + -y

/-- The additive group of degree-zero homogeneous fractions.

The common-denominator operations make the homogeneous fraction quotient an additive
commutative group. -/
noncomputable instance instAddCommGroup : AddCommGroup (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  add := add
  zero := zero (S := S)
  neg := neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [one_smul]
    module
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [one_smul]
    module
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [one_smul]
    module
  neg_add_cancel := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [one_smul]
    module
  add_comm := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [one_smul]
    module
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  zsmul_zero' := by intro a; rfl
  zsmul_succ' := by intro n a; rfl
  zsmul_neg' := by intro n a; rfl

/-- Scalar multiplication on homogeneous fraction representatives.

For a homogeneous scalar fraction a/b and module fraction m/s, form (a·m)/(bs). Their common
degree is the sum of the scalar and module representative degrees. -/
noncomputable def smulDef (r : HomogeneousLocalization.NumDenSameDeg 𝒜 S)
    (m : NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S) :
    NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S :=
  ⟨r.deg + m.deg,
   (r.num : R) • m.m, by
     have := M.gradedSMul
     have h := SetLike.GradedSMul.smul_mem r.num.2 m.m_mem
     have heq : (r.deg +ᵥ (m.deg : ℤ)) = (((r.deg + m.deg : ℕ) : ℤ)) := by
       change (m.deg : ℤ) + ((r.deg : ℕ) : ℤ) = (((r.deg + m.deg : ℕ) : ℤ))
       rw [add_comm, Nat.cast_add]
     rwa [heq] at h,
   (r.den : R) * m.s, by
     exact SetLike.GradedMul.mul_mem r.den.2 m.s_mem,
   Submonoid.mul_mem _ r.den_mem m.s_in_S⟩

/-- The action of the homogeneous localization ring on module fractions.

The representative rule (a/b)·(m/s) = (a·m)/(bs) descends to the homogeneous localization ring
and the module fraction quotient. -/
noncomputable def smul (r : HomogeneousLocalization 𝒜 S)
    (x : AtPrimeModuleCarrier (𝒜 := 𝒜) M S) :
    AtPrimeModuleCarrier (𝒜 := 𝒜) M S :=
  Quotient.liftOn₂ r x
    (fun rND mND => mk (M := M) (S := S) (smulDef (M := M) rND mND))
    (by
      intro r₁ m₁ r₂ m₂ hR hM
      obtain ⟨t₂, ht₂, e₂⟩ := hM
      have hEmb : HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 S r₁
          = HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 S r₂ := hR
      simp only [HomogeneousLocalization.NumDenSameDeg.embedding] at hEmb
      rw [Localization.mk_eq_mk', IsLocalization.eq] at hEmb
      obtain ⟨c, hc⟩ := hEmb
      refine Quotient.sound ⟨(c : R) * t₂, Submonoid.mul_mem _ c.2 ht₂, ?_⟩
      change ((c : R) * t₂) • ((((r₂.den : R)) * m₂.s) • (((r₁.num : R)) • m₁.m)
          - ((((r₁.den : R)) * m₁.s) • (((r₂.num : R)) • m₂.m))) = 0
      have key : ((((r₂.den : R)) * m₂.s) • (((r₁.num : R)) • m₁.m)
            - ((((r₁.den : R)) * m₁.s) • (((r₂.num : R)) • m₂.m) : M.carrier))
          = ((((r₂.den : R)) * (r₁.num : R)) • (m₂.s • m₁.m - m₁.s • m₂.m)
            + ((((r₂.den : R)) * (r₁.num : R)) - (((r₁.den : R)) * (r₂.num : R)))
              • (m₁.s • m₂.m)) := by module
      have hcz : (c : R) * ((((r₂.den : R)) * (r₁.num : R))
          - (((r₁.den : R)) * (r₂.num : R))) = 0 := by
        rw [mul_sub, hc, sub_self]
      have z1 : ((c : R) * t₂) • (((((r₂.den : R)) * (r₁.num : R))
          • (m₂.s • m₁.m - m₁.s • m₂.m) : M.carrier)) = 0 := by
        have hj : ((c : R) * t₂) • (((((r₂.den : R)) * (r₁.num : R))
            • (m₂.s • m₁.m - m₁.s • m₂.m) : M.carrier))
            = (((c : R) * (((r₂.den : R)) * (r₁.num : R)))
              • (t₂ • (m₂.s • m₁.m - m₁.s • m₂.m))) := by module
        rw [hj, e₂, smul_zero]
      have z2 : ((c : R) * t₂) • ((((((r₂.den : R)) * (r₁.num : R))
          - (((r₁.den : R)) * (r₂.num : R))) • (m₁.s • m₂.m) : M.carrier)) = 0 := by
        have hj : ((c : R) * t₂) • ((((((r₂.den : R)) * (r₁.num : R))
            - (((r₁.den : R)) * (r₂.num : R))) • (m₁.s • m₂.m) : M.carrier))
            = (t₂ • ((((c : R) * ((((r₂.den : R)) * (r₁.num : R))
              - (((r₁.den : R)) * (r₂.num : R))))) • (m₁.s • m₂.m))) := by module
        rw [hj, hcz, zero_smul, smul_zero]
      rw [key, smul_add, z1, z2, add_zero])

/-- The scalar action structure on homogeneous fraction classes.

The ring HomogeneousLocalization 𝒜 S acts by multiplying numerators and denominators of
representatives. -/
noncomputable instance instSMul : SMul (HomogeneousLocalization 𝒜 S)
    (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  smul := smul

/-- The module over the homogeneous localization ring.

The additive homogeneous fraction quotient is a module over HomogeneousLocalization 𝒜 S, with
scalar action induced by (a/b)·(m/s) = (a·m)/(bs). -/
noncomputable instance instModule : Module (HomogeneousLocalization 𝒜 S)
    (AtPrimeModuleCarrier (𝒜 := 𝒜) M S) where
  smul := smul
  one_smul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro m
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [smulDef, one_smul, one_mul,
      HomogeneousLocalization.NumDenSameDeg.num_one,
      HomogeneousLocalization.NumDenSameDeg.den_one]
    module
  mul_smul := by
    intro a b x
    obtain ⟨aND, rfl⟩ := HomogeneousLocalization.mk_surjective a
    obtain ⟨bND, rfl⟩ := HomogeneousLocalization.mk_surjective b
    refine Quotient.inductionOn x ?_
    intro m
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [smulDef, one_smul,
      HomogeneousLocalization.NumDenSameDeg.num_mul,
      HomogeneousLocalization.NumDenSameDeg.den_mul]
    module
  smul_zero := by
    intro r
    obtain ⟨rND, rfl⟩ := HomogeneousLocalization.mk_surjective r
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [smulDef, one_smul]
    module
  smul_add := by
    intro r x y
    obtain ⟨rND, rfl⟩ := HomogeneousLocalization.mk_surjective r
    refine Quotient.inductionOn x ?_
    intro m₁
    refine Quotient.inductionOn y ?_
    intro m₂
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [smulDef, one_smul]
    module
  add_smul := by
    intro r s x
    obtain ⟨rND, rfl⟩ := HomogeneousLocalization.mk_surjective r
    obtain ⟨sND, rfl⟩ := HomogeneousLocalization.mk_surjective s
    refine Quotient.inductionOn x ?_
    intro m
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [smulDef, one_smul,
      HomogeneousLocalization.NumDenSameDeg.num_add,
      HomogeneousLocalization.NumDenSameDeg.den_add]
    module
  zero_smul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro m
    refine Quotient.sound ⟨1, Submonoid.one_mem _, ?_⟩
    simp only [smulDef, one_smul, one_mul,
      HomogeneousLocalization.NumDenSameDeg.num_zero,
      HomogeneousLocalization.NumDenSameDeg.den_zero]
    module

/-- The map on homogeneous fractions induced by a graded morphism.

For a degree-preserving linear map f : M → N, the induced function on fraction classes sends
m/s to f(m)/s. -/
noncomputable def map {M N : GradedModuleCat (𝒜 := 𝒜)} (f : HomStruct M N)
    (S : Submonoid R) :
    AtPrimeModuleCarrier (𝒜 := 𝒜) M S → AtPrimeModuleCarrier (𝒜 := 𝒜) N S :=
  Quotient.lift
    (fun (c : NumDenSameDegModuleAtPrime (𝒜 := 𝒜) M S) =>
      mk (M := N) (S := S) ⟨c.deg, f.val c.m, f.property _ _ c.m_mem, c.s, c.s_mem, c.s_in_S⟩)
    (by
      intro a b hab
      obtain ⟨t, ht, h⟩ := hab
      refine Quotient.sound ⟨t, ht, ?_⟩
      have hlin : (b.s • f.val a.m - a.s • f.val b.m : N.carrier)
          = f.val (b.s • a.m - a.s • b.m) := by
        simp [map_sub, map_smul]
      rw [hlin, ← map_smul, h, map_zero])

end AtPrimeModuleCarrier

/-!
# Integer shifts and the graded regular module

The shift M(n) retains its carrier and scalar action while reindexing its components as M(n)_i
= M_{i+n}. Translating the direct-sum decomposition gives the shifted decomposition. The ring
itself has its natural components in nonnegative integer degrees and zero components in
negative degrees.
-/

/-- The reindexed homogeneous decomposition of a shifted module.

For n ∈ ℤ, decompose x into the direct sum with i-th component M_{i+n}. The component at i is
the original homogeneous component at i+n. -/
noncomputable def shiftDecomposeAddHom (M : GradedModuleCat (𝒜 := 𝒜)) (n : ℤ) :
    M.carrier →+ (⨁ i, M.grade (i + n)) :=
  let e : ℤ → ℤ := fun j => j + n
  have he : Function.Injective e := by
    intro a b h
    dsimp [e] at h
    exact add_right_cancel h
  letI := M.decomposition
  let decomp : M.carrier →+ (⨁ j, M.grade j) := (decomposeAddEquiv M.grade).toAddMonoidHom
  let comap : (⨁ j, M.grade j) →+ (⨁ i, M.grade (e i)) :=
    { toFun := DFinsupp.comapDomain e he
      map_zero' := DFinsupp.comapDomain_zero e he
      map_add' := fun f g => DFinsupp.comapDomain_add e he f g }
  comap.comp decomp

/-- The direct-sum decomposition of shifted homogeneous components.

The family i ↦ M_{i+n} has the direct-sum decomposition obtained by translating integer
indices in the decomposition of M. -/
@[instance_reducible]
noncomputable def shiftDecomposition (M : GradedModuleCat (𝒜 := 𝒜)) (n : ℤ) :
    DirectSum.Decomposition (fun i => M.grade (i + n)) where
  decompose' := (shiftDecomposeAddHom M n).toFun
  left_inv := by
    intro x
    change DirectSum.coeAddMonoidHom (fun i => M.grade (i + n))
      ((shiftDecomposeAddHom M n) x) = x
    let := M.decomposition
    have hbij : Function.Bijective (Equiv.addRight n : ℤ ≃ ℤ) :=
      (Equiv.addRight n).bijective
    have hcomp : ∀ (y : M.carrier) (i : ℤ),
        ((shiftDecomposeAddHom M n) y) i
          = (DirectSum.decompose M.grade y) (i + n) :=
      fun y i => rfl
    refine DirectSum.Decomposition.inductionOn (ℳ := M.grade)
      (motive := fun y => DirectSum.coeAddMonoidHom (fun i => M.grade (i + n))
        ((shiftDecomposeAddHom M n) y) = y) ?_ ?_ ?_ x
    · simp
    · intro j v
      have hmem : (v : M.carrier) ∈ M.grade j := v.2
      obtain ⟨k, hk⟩ := hbij.2 j
      have hkn : k + n = j := by simpa using hk
      subst hkn
      have hdec := DirectSum.decompose_of_mem (ℳ := M.grade) hmem
      have hDsingle : ((shiftDecomposeAddHom M n) (v : M.carrier))
          = DirectSum.of _ k ⟨(v : M.carrier), hmem⟩ := by
        ext i
        rw [hcomp, hdec]
        by_cases h : k = i
        · subst h
          simp
        · have h2 : i + n ≠ k + n := by omega
          have h3 : i ≠ k := by omega
          simp [DirectSum.of_eq_of_ne _ _ _ h2, DirectSum.of_eq_of_ne _ _ _ h3]
      rw [hDsingle, DirectSum.coeAddMonoidHom_of]
    · intro a b ha hb
      simp [map_add, ha, hb]
  right_inv := by
    intro x
    change ((shiftDecomposeAddHom M n) (DirectSum.coeAddMonoidHom
      (fun i => M.grade (i + n)) x)) = x
    let := M.decomposition
    have hcomp : ∀ (y : M.carrier) (i : ℤ),
        ((shiftDecomposeAddHom M n) y) i
          = (DirectSum.decompose M.grade y) (i + n) :=
      fun y i => rfl
    refine DirectSum.induction_on x ?_ ?_ ?_
    · simp
    · intro i v
      have hmem : (v : M.carrier) ∈ M.grade (i + n) := v.2
      have hdec := DirectSum.decompose_of_mem (ℳ := M.grade) hmem
      rw [DirectSum.coeAddMonoidHom_of]
      ext j
      rw [hcomp, hdec]
      by_cases h : j = i
      · subst h
        simp
      · have h2 : j + n ≠ i + n := by omega
        simp [DirectSum.of_eq_of_ne _ _ _ h2, DirectSum.of_eq_of_ne _ _ _ h]
    · intro a b ha hb
      simp [map_add, ha, hb]

/-- The integer shift functor on graded modules.

For n ∈ ℤ, the shifted module M(n) has M(n)_i = M_{i+n}, with the same carrier and R-action. A
graded morphism retains its underlying map and preserves the shifted components. -/
noncomputable def shift (n : ℤ) : GradedModuleCat (𝒜 := 𝒜) ⥤ GradedModuleCat (𝒜 := 𝒜) where
  obj M :=
    { carrier := M.carrier
      addCommGroup := M.addCommGroup
      module := M.module
      grade := fun i => M.grade (i + n)
      decomposition := shiftDecomposition M n
      gradedSMul := by
        refine ⟨?_⟩
        intro i j ai bj ha hb
        have h := M.gradedSMul.smul_mem ha hb
        have heq : (i +ᵥ (j + n) : ℤ) = ((i +ᵥ j) + n) := by
          have h1 : (i +ᵥ (j + n) : ℤ) = (j + n) + (i : ℤ) := rfl
          have h2 : (i +ᵥ j : ℤ) = j + (i : ℤ) := rfl
          omega
        rwa [heq] at h }
  map {M N} f :=
    ⟨f.val, fun i x hx => f.property (i + n) x hx⟩
  map_id M := by
    apply HomStruct.ext
    rfl
  map_comp {X Y Z} f g := by
    apply HomStruct.ext
    rfl

/-- A ring homogeneous component as an additive subgroup.

For n ∈ ℕ, regard the SetLike component 𝒜_n as an additive subgroup of R. -/
abbrev toAddSubgroup (𝒜 : ℕ → σS) (n : ℕ) : AddSubgroup R :=
  AddSubgroup.ofClass (𝒜 n)

/-- Extension of a natural ring grading to integer degrees.

The integer component at z is 𝒜_{z.toNat} when z ≥ 0 and the zero subgroup when z < 0. -/
def gradedRingObjectGrade (𝒜 : ℕ → σS) : ℤ → AddSubgroup R :=
  fun z => if 0 ≤ z then AddSubgroup.ofClass (𝒜 z.toNat) else ⊥

/-- Embedding a natural ring component into its integer degree.

The map from 𝒜_n to the extended ring component at the integer n preserves the underlying
element and is additive. -/
noncomputable def toGradeHom (𝒜 : ℕ → σS) (n : ℕ) :
    ↥(𝒜 n) →+ ↥(gradedRingObjectGrade (𝒜 := 𝒜) (Int.ofNat n)) where
  toFun x := ⟨x.1, by
    have h0 : (0 : ℤ) ≤ Int.ofNat n := Int.natCast_nonneg n
    have h1 : (Int.ofNat n).toNat = n := by simp
    unfold gradedRingObjectGrade
    rw [ite_eq_left h0, h1]
    exact x.2⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' := by intro a b; apply Subtype.ext; rfl

omit [GradedRing 𝒜] in
/-- The extended ring grading in a natural-number degree.

At Int.ofNat n, the extended component equals 𝒜_n as an additive subgroup. -/
theorem gradedRingObjectGrade_intOfNat (n : ℕ) :
    gradedRingObjectGrade (𝒜 := 𝒜) (Int.ofNat n) = toAddSubgroup 𝒜 n := by
  unfold gradedRingObjectGrade
  simp

/-- The ring decomposition indexed by integer degrees.

Decompose R by its natural grading and insert each component 𝒜_n into the direct-sum component
at the integer n. -/
noncomputable def gradedRingObjectDecomposeAddHom :
    R →+ (⨁ z, ↥(gradedRingObjectGrade (𝒜 := 𝒜) z)) :=
  let decN : R →+ (⨁ n, ↥(𝒜 n)) := (decomposeAddEquiv 𝒜).toAddMonoidHom
  let emb :
      (⨁ n, ↥(𝒜 n)) →+
        (⨁ z, ↥(gradedRingObjectGrade (𝒜 := 𝒜) z)) :=
    DirectSum.toAddMonoid (fun n =>
      (DirectSum.of (fun z => ↥(gradedRingObjectGrade (𝒜 := 𝒜) z)) (Int.ofNat n)).comp
        (toGradeHom (𝒜 := 𝒜) n))
  emb.comp decN

/-- The regular ring as an integer-graded module.

Use R as its regular module, with the given grading in nonnegative integer degrees and zero
components in negative degrees. -/
noncomputable def gradedRingObject : GradedModuleCat (𝒜 := 𝒜) where
  carrier := R
  addCommGroup := inferInstance
  module := inferInstance
  grade := gradedRingObjectGrade (𝒜 := 𝒜)
  decomposition :=
    ( { decompose' := gradedRingObjectDecomposeAddHom.toFun
        left_inv := by
          have hR := DirectSum.decomposeRingEquiv 𝒜
          have hDecomp : gradedRingObjectDecomposeAddHom (𝒜 := 𝒜) =
              (DirectSum.toAddMonoid (fun n =>
                (DirectSum.of (fun z => ↥(gradedRingObjectGrade (𝒜 := 𝒜) z))
                  (Int.ofNat n)).comp (toGradeHom (𝒜 := 𝒜) n))).comp
              (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom := rfl
          have hCoe : ∀ y : (⨁ n, ↥(𝒜 n)),
              DirectSum.coeAddMonoidHom (gradedRingObjectGrade (𝒜 := 𝒜))
                ((DirectSum.toAddMonoid (fun n =>
                  (DirectSum.of (fun z => ↥(gradedRingObjectGrade (𝒜 := 𝒜) z))
                    (Int.ofNat n)).comp (toGradeHom (𝒜 := 𝒜) n))) y)
                = DirectSum.coeAddMonoidHom 𝒜 y := by
            intro y
            refine DirectSum.induction_on y ?_ ?_ ?_
            · simp
            · intro n a
              simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
                DirectSum.coeAddMonoidHom_of]
              rfl
            · intro a b ha hb
              simp only [map_add, ha, hb]
          intro x
          change DirectSum.coeAddMonoidHom _
            (gradedRingObjectDecomposeAddHom (𝒜 := 𝒜) x) = x
          rw [hDecomp, AddMonoidHom.comp_apply, hCoe]
          exact DirectSum.Decomposition.left_inv (ℳ := 𝒜) x
        right_inv := by
          have hDecomp : gradedRingObjectDecomposeAddHom (𝒜 := 𝒜) =
              (DirectSum.toAddMonoid (fun n =>
                (DirectSum.of (fun z => ↥(gradedRingObjectGrade (𝒜 := 𝒜) z))
                  (Int.ofNat n)).comp (toGradeHom (𝒜 := 𝒜) n))).comp
              (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom := rfl
          intro x
          refine DirectSum.induction_on x ?_ ?_ ?_
          · simp
          · intro z v
            by_cases hz : 0 ≤ z
            · obtain ⟨n, rfl⟩ : ∃ n : ℕ, Int.ofNat n = z :=
                ⟨z.toNat, Int.toNat_of_nonneg hz⟩
              have hgrade : gradedRingObjectGrade (𝒜 := 𝒜) (Int.ofNat n) =
                  AddSubgroup.ofClass (𝒜 n) := by
                have htn : (Int.ofNat n).toNat = n := by simp
                unfold gradedRingObjectGrade
                rw [ite_eq_left hz, htn]
              have hv : (v : R) ∈ AddSubgroup.ofClass (𝒜 n) := hgrade ▸ v.2
              have hv' : (v : R) ∈ 𝒜 n := hv
              have hcoe : DirectSum.coeAddMonoidHom
                  (gradedRingObjectGrade (𝒜 := 𝒜))
                  (DirectSum.of _ (Int.ofNat n) v) = (v : R) :=
                DirectSum.coeAddMonoidHom_of _ _ _
              have hdec : DirectSum.decompose 𝒜 (v : R) =
                  DirectSum.of _ n ⟨(v : R), hv'⟩ :=
                DirectSum.decompose_of_mem (ℳ := 𝒜) hv'
              have hdec' : (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom (v : R) =
                  DirectSum.of _ n ⟨(v : R), hv'⟩ := hdec
              have hemb : (DirectSum.toAddMonoid (fun n =>
                  (DirectSum.of (fun z => ↥(gradedRingObjectGrade (𝒜 := 𝒜) z))
                    (Int.ofNat n)).comp (toGradeHom (𝒜 := 𝒜) n)))
                  (DirectSum.of _ n ⟨(v : R), hv'⟩)
                  = DirectSum.of _ (Int.ofNat n) v := by
                simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
                congr 1
              change ⇑(gradedRingObjectDecomposeAddHom (𝒜 := 𝒜))
                  (DirectSum.coeAddMonoidHom _
                    (DirectSum.of _ (Int.ofNat n) v)) = _
              rw [hDecomp, AddMonoidHom.comp_apply, hcoe, hdec', hemb]
            · have hgrade : gradedRingObjectGrade (𝒜 := 𝒜) z = ⊥ := by
                unfold gradedRingObjectGrade
                rw [ite_eq_right hz]
              have hv0 : (v : R) = 0 := AddSubgroup.mem_bot.mp (hgrade ▸ v.2)
              have hvsub : v = 0 := Subtype.ext hv0
              subst hvsub
              simp
          · intro a b ha hb
            have ha' : ⇑(gradedRingObjectDecomposeAddHom (𝒜 := 𝒜))
                (DirectSum.coeAddMonoidHom _ a) = a := ha
            have hb' : ⇑(gradedRingObjectDecomposeAddHom (𝒜 := 𝒜))
                (DirectSum.coeAddMonoidHom _ b) = b := hb
            change ⇑(gradedRingObjectDecomposeAddHom (𝒜 := 𝒜)) _ = _
            simp only [map_add, ha', hb'] } :
        DirectSum.Decomposition (gradedRingObjectGrade (𝒜 := 𝒜)) )
  gradedSMul := by
    refine ⟨?_⟩
    intro i j a b ha hb
    by_cases hj : 0 ≤ j
    · have hgrade_j : gradedRingObjectGrade (𝒜 := 𝒜) j = AddSubgroup.ofClass (𝒜 j.toNat) := by
        unfold gradedRingObjectGrade
        rw [ite_eq_left hj]
      have hb_sub : b ∈ AddSubgroup.ofClass (𝒜 j.toNat) := hgrade_j ▸ hb
      have hb' : b ∈ 𝒜 j.toNat := hb_sub
      have h_eq : i +ᵥ j = j + (i : ℤ) := rfl
      have h_nonneg : 0 ≤ i +ᵥ j := by
        rw [h_eq]
        have hi : 0 ≤ (i : ℤ) := Int.natCast_nonneg i
        omega
      have hgrade_ij : gradedRingObjectGrade (𝒜 := 𝒜) (i +ᵥ j) =
          AddSubgroup.ofClass (𝒜 (i +ᵥ j).toNat) := by
        unfold gradedRingObjectGrade
        rw [ite_eq_left h_nonneg]
      have htoNat : (i +ᵥ j).toNat = i + j.toNat := by
        rw [h_eq, Int.toNat_add hj (Int.natCast_nonneg i), Int.toNat_natCast,
          add_comm]
      rw [hgrade_ij, htoNat, smul_eq_mul _ _]
      exact SetLike.GradedMul.mul_mem (A := 𝒜) ha hb'
    · have hlt : j < 0 := by omega
      have hgrade_neg : gradedRingObjectGrade (𝒜 := 𝒜) j = ⊥ := by
        unfold gradedRingObjectGrade
        rw [ite_eq_right (by omega : ¬ 0 ≤ j)]
      have hb0 : b = 0 := AddSubgroup.mem_bot.mp (hgrade_neg ▸ hb)
      rw [hb0, smul_zero]
      exact (gradedRingObjectGrade (𝒜 := 𝒜) (i +ᵥ j)).zero_mem

omit [GradedRing 𝒜] in
/-- Nonnegative components of the graded regular ring.

For n ≥ 0 in ℤ, the homogeneous component of the extended ring grading is 𝒜_{n.toNat}. -/
theorem gradedRingObject_grade_of_nonneg (n : ℤ) (h : 0 ≤ n) :
    gradedRingObjectGrade (𝒜 := 𝒜) n = toAddSubgroup 𝒜 n.toNat := by
  unfold gradedRingObjectGrade
  simp [ite_eq_left h]

omit [GradedRing 𝒜] in
/-- Negative components of the graded regular ring.

For n < 0, the extended ring grading has zero homogeneous component. -/
theorem gradedRingObject_grade_of_neg (n : ℤ) (h : n < 0) :
    gradedRingObjectGrade (𝒜 := 𝒜) n = ⊥ := by
  have h' : ¬ (0 ≤ n) := by omega
  unfold gradedRingObjectGrade
  simp [ite_eq_right h']

end GradedModuleCat
end

@[expose] public section

namespace GradedModuleCat

universe u v

open scoped GradedModuleCat

variable {R : Type u} [CommRing R] {σS : Type v} [SetLike σS R]
  [AddSubgroupClass σS R] {𝒜 : ℕ → σS} [GradedRing 𝒜]

/-- Homogeneous multiplication between shifts of the graded ring.

For a ∈ 𝒜_m and n ∈ ℤ, multiplication x ↦ a·x defines a graded R-linear morphism R(n) →
R(n+m). A source element of degree i+n is sent to degree i+n+m. -/
noncomputable def shiftRingSmulHom (n : ℤ) (m : ℕ) (a : ↥(𝒜 m)) :
    GradedModuleCat.HomStruct
      ((GradedModuleCat.shift n).obj (GradedModuleCat.gradedRingObject (𝒜 := 𝒜)))
      ((GradedModuleCat.shift (n + (m : ℤ))).obj
        (GradedModuleCat.gradedRingObject (𝒜 := 𝒜))) where
  val :=
    { toFun := fun x => (a.1 : R) • x
      map_add' := by intro x y; exact smul_add _ _ _
      map_smul' := by
        intro r x
        change (a.1 : R) • (r • x) = r • ((a.1 : R) • x)
        exact smul_comm _ _ _ }
  property := by
    intro i x hx
    have ha : (a.1 : R) ∈ 𝒜 m := a.2
    have h :=
      (GradedModuleCat.gradedRingObject (𝒜 := 𝒜)).gradedSMul.smul_mem ha hx
    have heq : (m +ᵥ (i + n) : ℤ) = i + (n + (m : ℤ)) := by
      have h1 : (m +ᵥ (i + n) : ℤ) = (i + n) + (m : ℤ) := rfl
      omega
    rwa [heq] at h

end GradedModuleCat
