/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheoryPolynomialLiftIndependence

set_option autoImplicit false

/-! Tests for independence of the obstruction class from the polynomial lift. -/

open CategoryTheory Opposite Simplicial
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory
open WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted

namespace MathlibExtTest.AlgebraicGeometry.AffinePerfectObstructionTheoryPolynomialLiftIndependence

/-- The constant simplicial algebra on `k[X]`. -/
noncomputable abbrev constPoly (k : Type) [Field k] : SimplicialObject (CommAlgCat.{0} k) :=
  (SimplicialObject.const (CommAlgCat.{0} k)).obj (CommAlgCat.of k (MvPolynomial (Fin 1) k))

/-- `k[X]` over `k`, resolved by the constant simplicial algebra on itself with the identity
augmentation. -/
noncomputable abbrev polyResolution (k : Type) [Field k] :
    PolynomialResolution k (MvPolynomial (Fin 1) k) where
  algebra := constPoly k
  augmentation := 𝟙 _
  polynomial _ := ⟨Fin 1, ⟨AlgEquiv.refl⟩⟩
  surjective _ := Function.surjective_id
  augmentation_quasiIso := inferInstance

/-- Dual numbers over `B`: pairs with `(a, m) * (b, n) = (a * b, a * n + b * m)`. -/
@[ext]
structure DualNumbers (B : Type) where
  fst : B
  snd : B

namespace DualNumbers

variable {B : Type} [CommRing B]

def add (x y : DualNumbers B) : DualNumbers B := ⟨x.fst + y.fst, x.snd + y.snd⟩
def neg (x : DualNumbers B) : DualNumbers B := ⟨-x.fst, -x.snd⟩
def sub (x y : DualNumbers B) : DualNumbers B := ⟨x.fst - y.fst, x.snd - y.snd⟩
def mul (x y : DualNumbers B) : DualNumbers B :=
  ⟨x.fst * y.fst, x.fst * y.snd + y.fst * x.snd⟩
def nsmul (n : ℕ) (x : DualNumbers B) : DualNumbers B := ⟨n • x.fst, n • x.snd⟩
def zsmul (z : ℤ) (x : DualNumbers B) : DualNumbers B := ⟨z • x.fst, z • x.snd⟩

instance : Zero (DualNumbers B) := ⟨⟨0, 0⟩⟩
instance : One (DualNumbers B) := ⟨⟨1, 0⟩⟩
instance : Add (DualNumbers B) := ⟨DualNumbers.add⟩
instance : Neg (DualNumbers B) := ⟨DualNumbers.neg⟩
instance : Sub (DualNumbers B) := ⟨DualNumbers.sub⟩
instance : Mul (DualNumbers B) := ⟨DualNumbers.mul⟩

@[simp] theorem fst_zero : (0 : DualNumbers B).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : DualNumbers B).snd = 0 := rfl
@[simp] theorem fst_one : (1 : DualNumbers B).fst = 1 := rfl
@[simp] theorem snd_one : (1 : DualNumbers B).snd = 0 := rfl
@[simp] theorem fst_add (x y : DualNumbers B) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : DualNumbers B) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_neg (x : DualNumbers B) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : DualNumbers B) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_sub (x y : DualNumbers B) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub (x y : DualNumbers B) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem fst_mul (x y : DualNumbers B) :
    (x * y).fst = x.fst * y.fst := rfl
@[simp] theorem snd_mul (x y : DualNumbers B) :
    (x * y).snd = x.fst * y.snd + y.fst * x.snd := rfl

instance : CommRing (DualNumbers B) where
  add_assoc := by intro x y z; ext <;> simp <;> ring
  zero_add := by intro x; ext <;> simp
  add_zero := by intro x; ext <;> simp
  add_comm := by intro x y; ext <;> simp <;> ring
  mul_assoc := by intro x y z; ext <;> simp <;> ring
  one_mul := by intro x; ext <;> simp
  mul_one := by intro x; ext <;> simp
  mul_comm := by intro x y; ext <;> simp <;> ring
  left_distrib := by intro x y z; ext <;> simp <;> ring
  right_distrib := by intro x y z; ext <;> simp <;> ring
  zero_mul := by intro x; ext <;> simp
  mul_zero := by intro x; ext <;> simp
  neg_add_cancel := by intro x; ext <;> simp
  nsmul := DualNumbers.nsmul
  nsmul_zero := by
    intro x
    ext
    · show (0 : ℕ) • x.fst = 0
      exact AddMonoid.nsmul_zero _
    · show (0 : ℕ) • x.snd = 0
      exact AddMonoid.nsmul_zero _
  nsmul_succ := by
    intro n x
    ext
    · show (n + 1) • x.fst = n • x.fst + x.fst
      exact AddMonoid.nsmul_succ _ _
    · show (n + 1) • x.snd = n • x.snd + x.snd
      exact AddMonoid.nsmul_succ _ _
  zsmul := DualNumbers.zsmul
  zsmul_zero' := by
    intro x
    ext
    · show (0 : ℤ) • x.fst = 0
      exact SubNegMonoid.zsmul_zero' _
    · show (0 : ℤ) • x.snd = 0
      exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' := by
    intro n x
    ext
    · show ((n.succ : ℕ) : ℤ) • x.fst = ((n : ℕ) : ℤ) • x.fst + x.fst
      exact SubNegMonoid.zsmul_succ' _ _
    · show ((n.succ : ℕ) : ℤ) • x.snd = ((n : ℕ) : ℤ) • x.snd + x.snd
      exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by
    intro n x
    ext
    · show (Int.negSucc n) • x.fst = -(((n.succ : ℕ) : ℤ) • x.fst)
      exact SubNegMonoid.zsmul_neg' _ _
    · show (Int.negSucc n) • x.snd = -(((n.succ : ℕ) : ℤ) • x.snd)
      exact SubNegMonoid.zsmul_neg' _ _
  sub_eq_add_neg := by
    intro x y
    ext <;> simp only [fst_sub, snd_sub, fst_add, snd_add, fst_neg, snd_neg, sub_eq_add_neg]

end DualNumbers

/-- Scalar action of `k` on dual numbers. -/
instance dualSMul {k B : Type} [CommRing k] [CommRing B] [Algebra k B] :
    SMul k (DualNumbers B) :=
  ⟨fun r x => ⟨r • x.fst, r • x.snd⟩⟩

@[simp] theorem fst_smul {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    (r : k) (x : DualNumbers B) : (r • x).fst = r • x.fst := rfl
@[simp] theorem snd_smul {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    (r : k) (x : DualNumbers B) : (r • x).snd = r • x.snd := rfl

/-- The algebra map into dual numbers. -/
def dualAlgebraMap {k B : Type} [CommRing k] [CommRing B] [Algebra k B] :
    k →+* DualNumbers B where
  toFun r := ⟨algebraMap k B r, 0⟩
  map_one' := by ext <;> simp
  map_mul' := by intro r s; ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intro r s; ext <;> simp

@[simp] theorem fst_algebraMap {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    (r : k) : (dualAlgebraMap r).fst = algebraMap k B r := rfl
@[simp] theorem snd_algebraMap {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    (r : k) : (dualAlgebraMap r).snd = (0 : B) := rfl

/-- The `k`-algebra structure on dual numbers. -/
instance dualAlgebra {k B : Type} [CommRing k] [CommRing B] [Algebra k B] :
    Algebra k (DualNumbers B) where
  algebraMap := dualAlgebraMap
  commutes' := by intro r x; ext <;> simp; ring
  smul_def' := by
    intro r x
    ext
    · show r • x.fst = algebraMap k B r * x.fst
      exact Algebra.smul_def _ _
    · show r • x.snd = algebraMap k B r * x.snd + x.fst * 0
      rw [mul_zero, add_zero]
      exact Algebra.smul_def _ _

/-- The projection dual numbers to `B` as a `k`-algebra map. -/
def dualFst {k B : Type} [CommRing k] [CommRing B] [Algebra k B] :
    DualNumbers B →ₐ[k] B where
  toFun x := x.fst
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

theorem dualFst_surjective {k B : Type} [CommRing k] [CommRing B] [Algebra k B] :
    Function.Surjective (dualFst (k := k) (B := B)) := fun b => ⟨⟨b, 0⟩, rfl⟩

/-- Dual numbers as a square-zero extension of `B`. -/
noncomputable def dualExtension (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] :
    Algebra.Extension.{0} k B :=
  Algebra.Extension.ofSurjective (dualFst (k := k) (B := B)) (dualFst_surjective (k := k) (B := B))

theorem dual_mul_eq_zero {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    {x y : DualNumbers B} (hx : DualNumbers.fst x = 0) (hy : DualNumbers.fst y = 0) :
    x * y = 0 := by
  ext <;> simp [hx, hy]

theorem dualExtension_ker_sq (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] :
    (dualExtension k B).ker ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have ha0 : DualNumbers.fst a = 0 := RingHom.mem_ker.mp ha
  have hb0 : DualNumbers.fst b = 0 := RingHom.mem_ker.mp hb
  exact dual_mul_eq_zero (k := k) ha0 hb0

theorem dual_ne_zero {B : Type} [CommRing B] [Nontrivial B] :
    (⟨0, 1⟩ : DualNumbers B) ≠ 0 := by
  intro hcon
  have h10 : (1 : B) = 0 := congrArg DualNumbers.snd hcon
  exact one_ne_zero h10

theorem dualExtension_ker_ne (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B]
    [Nontrivial B] : (dualExtension k B).ker ≠ ⊥ := by
  intro hker
  have hmem : (⟨0, 1⟩ : DualNumbers B) ∈ (dualExtension k B).ker :=
    RingHom.mem_ker.mpr rfl
  rw [hker] at hmem
  have hzero : (⟨0, 1⟩ : DualNumbers B) = 0 := Ideal.mem_bot.mp hmem
  exact dual_ne_zero hzero

/-- The algebra map sending `X` to `(X, 0)`. -/
noncomputable def liftFstHom (k : Type) [Field k] :
    MvPolynomial (Fin 1) k →ₐ[k] DualNumbers (MvPolynomial (Fin 1) k) :=
  MvPolynomial.aeval fun _ : Fin 1 =>
    (⟨MvPolynomial.X 0, 0⟩ : DualNumbers (MvPolynomial (Fin 1) k))

/-- The algebra map sending `X` to `(X, 1)`. -/
noncomputable def liftSndHom (k : Type) [Field k] :
    MvPolynomial (Fin 1) k →ₐ[k] DualNumbers (MvPolynomial (Fin 1) k) :=
  MvPolynomial.aeval fun _ : Fin 1 =>
    (⟨MvPolynomial.X 0, 1⟩ : DualNumbers (MvPolynomial (Fin 1) k))

/-- The lift sending `X` to `(X, 0)`. -/
noncomputable def liftFst (k : Type) [Field k] :
    PolynomialLift (polyResolution k) (dualExtension k (MvPolynomial (Fin 1) k)) where
  hom := liftFstHom k
  over := MvPolynomial.algHom_ext fun i => by
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have haeval : (liftFstHom k) (MvPolynomial.X 0)
        = (⟨MvPolynomial.X 0, 0⟩ : DualNumbers (MvPolynomial (Fin 1) k)) :=
      MvPolynomial.aeval_X (R := k) (S₁ := DualNumbers (MvPolynomial (Fin 1) k))
        (σ := Fin 1) _ _
    have hcomp : ((IsScalarTower.toAlgHom k (dualExtension k (MvPolynomial (Fin 1) k)).Ring
          (MvPolynomial (Fin 1) k)).comp (liftFstHom k)) (MvPolynomial.X 0)
        = (IsScalarTower.toAlgHom k (dualExtension k (MvPolynomial (Fin 1) k)).Ring
          (MvPolynomial (Fin 1) k)) ((liftFstHom k) (MvPolynomial.X 0)) := rfl
    rw [hcomp, haeval]
    rfl

/-- The lift sending `X` to `(X, 1)`. -/
noncomputable def liftSnd (k : Type) [Field k] :
    PolynomialLift (polyResolution k) (dualExtension k (MvPolynomial (Fin 1) k)) where
  hom := liftSndHom k
  over := MvPolynomial.algHom_ext fun i => by
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have haeval : (liftSndHom k) (MvPolynomial.X 0)
        = (⟨MvPolynomial.X 0, 1⟩ : DualNumbers (MvPolynomial (Fin 1) k)) :=
      MvPolynomial.aeval_X (R := k) (S₁ := DualNumbers (MvPolynomial (Fin 1) k))
        (σ := Fin 1) _ _
    have hcomp : ((IsScalarTower.toAlgHom k (dualExtension k (MvPolynomial (Fin 1) k)).Ring
          (MvPolynomial (Fin 1) k)).comp (liftSndHom k)) (MvPolynomial.X 0)
        = (IsScalarTower.toAlgHom k (dualExtension k (MvPolynomial (Fin 1) k)).Ring
          (MvPolynomial (Fin 1) k)) ((liftSndHom k) (MvPolynomial.X 0)) := rfl
    rw [hcomp, haeval]
    rfl

/-- The two lifts are distinct. -/
theorem lift_ne (k : Type) [Field k] : liftFst k ≠ liftSnd k := by
  intro hcon
  have hFst : (liftFst k).hom (MvPolynomial.X 0)
      = (⟨MvPolynomial.X 0, 0⟩ : DualNumbers (MvPolynomial (Fin 1) k)) :=
    MvPolynomial.aeval_X (R := k) (S₁ := DualNumbers (MvPolynomial (Fin 1) k))
      (σ := Fin 1) _ _
  have hSnd : (liftSnd k).hom (MvPolynomial.X 0)
      = (⟨MvPolynomial.X 0, 1⟩ : DualNumbers (MvPolynomial (Fin 1) k)) :=
    MvPolynomial.aeval_X (R := k) (S₁ := DualNumbers (MvPolynomial (Fin 1) k))
      (σ := Fin 1) _ _
  have hX : (liftFst k).hom (MvPolynomial.X 0)
      = (liftSnd k).hom (MvPolynomial.X 0) :=
    congrArg (fun L : PolynomialLift (polyResolution k)
      (dualExtension k (MvPolynomial (Fin 1) k)) => L.hom (MvPolynomial.X 0)) hcon
  rw [hFst, hSnd] at hX
  have h01 : (0 : MvPolynomial (Fin 1) k) = 1 := congrArg DualNumbers.snd hX
  exact zero_ne_one h01

/-- The kernel is nonzero on dual numbers over `k[X]`. -/
example (k : Type) [Field k] :
    (dualExtension k (MvPolynomial (Fin 1) k)).ker ≠ ⊥ :=
  dualExtension_ker_ne k (MvPolynomial (Fin 1) k)

/-- The obstruction class is independent of the lift on dual numbers over `k[X]`. -/
example (k : Type) [Field k] (T : PerfectObstructionTheory (polyResolution k))
    (C : CotangentExtensionCocycle (polyResolution k)
      (dualExtension k (MvPolynomial (Fin 1) k)) (liftFst k))
    (C' : CotangentExtensionCocycle (polyResolution k)
      (dualExtension k (MvPolynomial (Fin 1) k)) (liftSnd k)) :
    obstructionClass T C = obstructionClass T C' :=
  polynomial_lift_independence _ T _ (dualExtension_ker_sq k _) _ _ C C'

/-- Vanishing of the obstruction class transfers across polynomial lifts. -/
theorem vanishing_transfer (k : Type) [Field k]
    (T : PerfectObstructionTheory (polyResolution k))
    (C : CotangentExtensionCocycle (polyResolution k)
      (dualExtension k (MvPolynomial (Fin 1) k)) (liftFst k))
    (C' : CotangentExtensionCocycle (polyResolution k)
      (dualExtension k (MvPolynomial (Fin 1) k)) (liftSnd k))
    (h : obstructionClass T C = 0) : obstructionClass T C' = 0 := by
  rw [← polynomial_lift_independence _ T _ (dualExtension_ker_sq k _) _ _ C C']
  exact h

end MathlibExtTest.AlgebraicGeometry.AffinePerfectObstructionTheoryPolynomialLiftIndependence
