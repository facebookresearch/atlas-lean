/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.Free
public import MathlibExt.CategoryTheory.Comonad.BarResolution
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Polynomial comonads and augmented simplicial resolutions

Let `k` be a commutative ring. The free polynomial algebra and forgetful functors give a
comonad `T(A) = k[X_a | a ∈ A]` on commutative `k`-algebras. Its counit evaluates `X_a` at
`a`, and its comultiplication sends `X_a` to `X_{X_a}`.

The associated augmented simplicial resolution has degree `n` equal to `T^(n+1)(A)`, with
faces obtained by inserting the counit and degeneracies by inserting comultiplication.
Identifying a degree with the polynomial algebra on the preceding power gives explicit
formulas for its generators, all faces, degeneracies, augmentation, and algebra maps. The ring
and algebra-carrier universes are independent, with carrier universe `max u v`.

Reference: Weibel, *An Introduction to Homological Algebra*, Example 8.6.16. The adjunction-
to-comonad construction is due to Kim Morrison and Bhavik Mehta.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- The free-polynomial comonad on commutative algebras.

For a commutative ring `k`, the free/forgetful adjunction gives the comonad `T` with `T(A) =
MvPolynomial A k`, counit polynomial evaluation, and comultiplication variable insertion. -/
def polynomialComonad : Comonad (CommAlgCat.{max u v} k) :=
  (freeForgetAdjunction.{u, v} k).toComonad

/-- The functor underlying the polynomial comonad.

The underlying functor forgets a commutative `k`-algebra to its carrier and forms the free
polynomial `k`-algebra on that carrier. -/
@[simp]
theorem polynomialComonad_toFunctor :
    (polynomialComonad.{u, v} k).toFunctor =
      forget (CommAlgCat.{max u v} k) ⋙ free.{u, v} k := rfl

/-- The carrier of a polynomial comonad object.

For a commutative `k`-algebra `A`, the carrier of `T(A)` is `MvPolynomial A k`. -/
@[simp]
theorem polynomialComonad_obj_carrier (A : CommAlgCat.{max u v} k) :
    ↥((polynomialComonad.{u, v} k).obj A) = MvPolynomial A k := rfl

/-- The variable formula for the polynomial adjunction unit.

For `a ∈ A`, the free/forgetful adjunction unit sends `a` to the polynomial variable `X_a`. -/
theorem polynomialComonad_unit_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((freeForgetAdjunction.{u, v} k).unit.app A) a = MvPolynomial.X a := rfl

/-- The renaming homomorphism of the polynomial comonad.

For `f : A → B`, the comonad map `T(f)` is polynomial variable renaming along the underlying
function of `f`. -/
@[simp]
theorem polynomialComonad_map_hom {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    ((polynomialComonad.{u, v} k).map f).hom = MvPolynomial.rename (R := k) f.hom := rfl

/-- The variable formula for polynomial comonad maps.

For `f : A → B` and `a ∈ A`, the map `T(f)` sends `X_a` to `X_{f(a)}`. -/
theorem polynomialComonad_map_X {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) (a : A) :
    ((polynomialComonad.{u, v} k).map f).hom (MvPolynomial.X a) =
      MvPolynomial.X (f.hom a) := MvPolynomial.rename_X f.hom a

/-- The polynomial evaluation counit.

For `A`, the counit `T(A) → A` is the `k`-algebra evaluation map at the family `a ↦ a`. -/
@[simp]
theorem polynomialComonad_counit_hom (A : CommAlgCat.{max u v} k) :
    ((polynomialComonad.{u, v} k).ε.app A).hom =
      MvPolynomial.aeval (R := k) (fun a : A => a) := rfl

/-- The counit on a polynomial variable.

The counit `T(A) → A` sends `X_a` to `a`. -/
theorem polynomialComonad_counit_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((polynomialComonad.{u, v} k).ε.app A).hom (MvPolynomial.X a) = a :=
  MvPolynomial.aeval_X (fun a : A => a) a

/-- The counit on a polynomial constant.

For `c ∈ k`, the counit sends the constant polynomial `C(c)` to its scalar image in `A`. -/
theorem polynomialComonad_counit_C (A : CommAlgCat.{max u v} k) (c : k) :
    ((polynomialComonad.{u, v} k).ε.app A).hom (MvPolynomial.C c) = algebraMap k A c :=
  MvPolynomial.aeval_C (fun a : A => a) c

/-- The variable-renaming comultiplication.

The comultiplication `T(A) → T²(A)` renames the variable indexed by `a ∈ A` to the variable
indexed by `X_a ∈ T(A)`. -/
@[simp]
theorem polynomialComonad_comultiplication_hom (A : CommAlgCat.{max u v} k) :
    ((polynomialComonad.{u, v} k).δ.app A).hom =
      MvPolynomial.rename (R := k) (fun a : A => (MvPolynomial.X a : MvPolynomial A k)) := rfl

/-- The comultiplication on a polynomial variable.

For `a ∈ A`, the comultiplication sends `X_a` to the iterated variable `X_{X_a}`. -/
theorem polynomialComonad_comultiplication_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((polynomialComonad.{u, v} k).δ.app A).hom (MvPolynomial.X a) =
      MvPolynomial.X (MvPolynomial.X a : MvPolynomial A k) :=
  MvPolynomial.rename_X (fun a : A => (MvPolynomial.X a : MvPolynomial A k)) a

/-- Naturality of polynomial evaluation.

For `f : A → B`, renaming by `f` and then evaluating in `B` equals evaluating in `A` and then
applying `f`. -/
@[reassoc]
theorem polynomialComonad_counit_naturality {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialComonad.{u, v} k).map f ≫ (polynomialComonad.{u, v} k).ε.app B =
      (polynomialComonad.{u, v} k).ε.app A ≫ f :=
  (polynomialComonad.{u, v} k).ε.naturality f

/-- Naturality of polynomial variable insertion.

For `f : A → B`, comultiplication commutes with `T(f)` and the twice-applied map `T²(f)`. -/
@[reassoc]
theorem polynomialComonad_comultiplication_naturality
    {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialComonad.{u, v} k).map f ≫ (polynomialComonad.{u, v} k).δ.app B =
      (polynomialComonad.{u, v} k).δ.app A ≫
        (polynomialComonad.{u, v} k).map ((polynomialComonad.{u, v} k).map f) :=
  (polynomialComonad.{u, v} k).δ.naturality f

/-- The powers of the polynomial comonad.

For `n ∈ ℕ`, this is the iterated functor `T^n` on commutative `k`-algebras, including the
identity power at `n = 0`. -/
abbrev polynomialPower (n : ℕ) : CommAlgCat.{max u v} k ⥤ CommAlgCat.{max u v} k :=
  Comonad.comonadPow (polynomialComonad.{u, v} k) n

/-- The polynomial object of a successor comonad power.

The object `T^(n+1)(A)` is the polynomial algebra over `k` with variables indexed by the
carrier of `T^n(A)`. -/
theorem polynomialPower_succ_obj (n : ℕ) (A : CommAlgCat.{max u v} k) :
    (polynomialPower.{u, v} k (n + 1)).obj A =
      CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) :=
  Comonad.comonadPow_succ_obj_eq (polynomialComonad.{u, v} k) n A

/-- The polynomial comparison for a successor power.

This isomorphism identifies `T^(n+1)(A)` with `MvPolynomial (T^n(A)) k`. -/
def polynomialPowerObjIso (n : ℕ) (A : CommAlgCat.{max u v} k) :
    (polynomialPower.{u, v} k (n + 1)).obj A ≅
      CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) :=
  eqToIso (polynomialPower_succ_obj.{u, v} k n A)

/-- Naturality of the successor-power polynomial comparison.

For `f : A → B`, the comparison identifies `T^(n+1)(f)` with polynomial renaming along
`T^n(f)`. -/
@[reassoc]
theorem polynomialPowerObjIso_naturality (n : ℕ)
    {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialPower.{u, v} k (n + 1)).map f ≫ (polynomialPowerObjIso.{u, v} k n B).hom =
      (polynomialPowerObjIso.{u, v} k n A).hom ≫
        (polynomialComonad.{u, v} k).map ((polynomialPower.{u, v} k n).map f) := by
  induction n generalizing A B with
  | zero =>
    change (polynomialComonad.{u, v} k).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (polynomialComonad.{u, v} k).map f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih =>
    exact ih ((polynomialComonad.{u, v} k).map f)

/-- The augmented polynomial resolution functor.

The polynomial comonad assigns to each commutative `k`-algebra `A` an augmented simplicial
algebra with degree `n` equal to `T^(n+1)(A)`. -/
def polynomialResolutionFunctor :
    CommAlgCat.{max u v} k ⥤ SimplicialObject.Augmented (CommAlgCat.{max u v} k) :=
  Comonad.resolutionAugmentedFunctor (polynomialComonad.{u, v} k)

/-- The augmented polynomial resolution of an algebra.

For `A`, this is the comonad resolution `P_•(A) → A`, whose degree-`n` algebra is
`T^(n+1)(A)`. -/
abbrev polynomialResolution (A : CommAlgCat.{max u v} k) :
    SimplicialObject.Augmented (CommAlgCat.{max u v} k) :=
  (polynomialResolutionFunctor.{u, v} k).obj A

/-- The polynomial resolution map of an algebra homomorphism.

For `f : A → B`, this is the augmented simplicial map from the polynomial resolution of `A` to
that of `B`, with degree-`n` map `T^(n+1)(f)`. -/
abbrev polynomialResolutionMap {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    polynomialResolution.{u, v} k A ⟶ polynomialResolution.{u, v} k B :=
  (polynomialResolutionFunctor.{u, v} k).map f

/-- The augmentation target of a polynomial resolution.

The augmentation target of the polynomial resolution of `A` is `A`. -/
@[simp]
theorem polynomialResolution_point (A : CommAlgCat.{max u v} k) :
    (polynomialResolution.{u, v} k A).right = A :=
  Comonad.resolutionAugmented_point (polynomialComonad.{u, v} k) A

/-- The simplicial algebra underlying a polynomial resolution.

The underlying simplicial object is the bar resolution of `A` for the polynomial comonad. -/
@[simp]
theorem polynomialResolution_left (A : CommAlgCat.{max u v} k) :
    (polynomialResolution.{u, v} k A).left =
      Comonad.resolutionBar (polynomialComonad.{u, v} k) A :=
  Comonad.resolutionAugmented_left (polynomialComonad.{u, v} k) A

/-- The degree formula for a polynomial resolution.

For `n ∈ ℕ`, the degree-`n` algebra of the polynomial resolution of `A` is `T^(n+1)(A)`. -/
@[simp]
theorem polynomialResolution_obj (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) =
      (polynomialPower.{u, v} k (n + 1)).obj A := rfl

/-- The degreewise polynomial-algebra comparison.

Degree `n` of the polynomial resolution is canonically isomorphic to the polynomial algebra on
the carrier of `T^n(A)`. -/
def polynomialResolutionObjIso (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ≅
      CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) :=
  Comonad.resolutionBarObjIso (polynomialComonad.{u, v} k) A n ≪≫
    polynomialPowerObjIso.{u, v} k n A

/-- The forward map of the degreewise polynomial comparison.

The forward degree-`n` comparison is the successor-power polynomial comparison `T^(n+1)(A) →
MvPolynomial (T^n(A)) k`. -/
@[simp]
theorem polynomialResolutionObjIso_hom (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolutionObjIso.{u, v} k A n).hom =
      (polynomialPowerObjIso.{u, v} k n A).hom := by
  change 𝟙 _ ≫ (polynomialPowerObjIso.{u, v} k n A).hom = _
  exact Category.id_comp _

/-- The inverse map of the degreewise polynomial comparison.

The inverse degree-`n` comparison is the inverse successor-power polynomial comparison. -/
@[simp]
theorem polynomialResolutionObjIso_inv (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolutionObjIso.{u, v} k A n).inv =
      (polynomialPowerObjIso.{u, v} k n A).inv := by
  change (polynomialPowerObjIso.{u, v} k n A).inv ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The degreewise map of polynomial resolutions.

For `f : A → B`, the degree-`n` component of the induced resolution map is `T^(n+1)(f)`. -/
@[simp]
theorem polynomialResolutionMap_left_app {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) :
    (polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n)) =
      (polynomialPower.{u, v} k (n + 1)).map f :=
  Comonad.resolutionHom_left_app (polynomialComonad.{u, v} k) f n

/-- The augmentation-target map of polynomial resolutions.

For `f : A → B`, the map on augmentation targets of the induced resolution map is `f`. -/
@[simp]
theorem polynomialResolutionMap_right {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialResolutionMap.{u, v} k f).right = f := rfl

/-- Naturality of the degreewise polynomial-algebra comparison.

The degree-`n` comparison carries the resolution map induced by `f : A → B` to polynomial
renaming along `T^n(f)`. -/
@[reassoc]
theorem polynomialResolutionObjIso_naturality {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) :
    (polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n)) ≫
        (polynomialResolutionObjIso.{u, v} k B n).hom =
      (polynomialResolutionObjIso.{u, v} k A n).hom ≫
        (polynomialComonad.{u, v} k).map ((polynomialPower.{u, v} k n).map f) := by
  change (polynomialPower.{u, v} k (n + 1)).map f ≫
      (polynomialPowerObjIso.{u, v} k n B).hom =
    (polynomialPowerObjIso.{u, v} k n A).hom ≫
      (polynomialComonad.{u, v} k).map ((polynomialPower.{u, v} k n).map f)
  exact polynomialPowerObjIso_naturality.{u, v} k n f

/-- Counit insertion for polynomial resolution faces.

For `i : Fin (n+2)`, the face `d_i : P_(n+1)(A) → P_n(A)` is the counit insertion
`cobarEpsilonAtPos T (n+1) i A`, with the indicated simplicial index order. -/
@[simp]
theorem polynomialResolution_map_δ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 2)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i).op =
      Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) (n + 1) i A :=
  Comonad.resolutionBar_map_δ_op (polynomialComonad.{u, v} k) A i

/-- Comultiplication insertion for polynomial resolution degeneracies.

For `i : Fin (n+1)`, the degeneracy `s_i : P_n(A) → P_(n+1)(A)` is the comultiplication
insertion `cobarDeltaAtPos T (n+1) i A`. -/
@[simp]
theorem polynomialResolution_map_σ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i).op =
      Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A :=
  Comonad.resolutionBar_map_σ_op (polynomialComonad.{u, v} k) A i

/-- The degree-zero polynomial augmentation.

The degree-zero augmentation `T(A) → A` is the polynomial evaluation counit. -/
@[simp]
theorem polynomialResolution_augmentation_zero (A : CommAlgCat.{max u v} k) :
    (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk 0)) =
      (polynomialComonad.{u, v} k).ε.app A :=
  Comonad.resolutionAugmented_hom_zero (polynomialComonad.{u, v} k) A

/-- Compatibility of polynomial resolution operators with augmentation.

For any simplicial operator from degree `m` to degree `n`, applying the operator and then
augmenting to `A` equals augmenting directly from degree `m`. -/
@[reassoc]
theorem polynomialResolution_augmentation_naturality (A : CommAlgCat.{max u v} k)
    {m n : ℕ} (f : op (SimplexCategory.mk m) ⟶ op (SimplexCategory.mk n)) :
    (polynomialResolution.{u, v} k A).left.map f ≫
        (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n)) =
      (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk m)) :=
  ((polynomialResolution.{u, v} k A).hom.naturality f).trans (Category.comp_id _)

/-- The polynomial generator in a resolution degree.

For `x ∈ T^n(A)`, this is the element of `T^(n+1)(A)` corresponding to the variable `X_x`
under the degreewise polynomial comparison. -/
def polynomialResolutionGenerator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k n).obj A) :
    (polynomialPower.{u, v} k (n + 1)).obj A :=
  (polynomialPowerObjIso.{u, v} k n A).inv.hom (MvPolynomial.X x)

/-- The degreewise comparison on polynomial generators.

The degree-`n` polynomial comparison sends the generator indexed by `x ∈ T^n(A)` to the
variable `X_x`. -/
theorem polynomialResolutionObjIso_hom_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k n).obj A) :
    (polynomialResolutionObjIso.{u, v} k A n).hom.hom
        (polynomialResolutionGenerator.{u, v} k A n x) = MvPolynomial.X x :=
  CommAlgCat.hom_inv_apply (polynomialResolutionObjIso.{u, v} k A n) (MvPolynomial.X x)

/-- The polynomial generator in degree zero.

For `a ∈ A`, the degree-zero generator indexed by `a` is `X_a ∈ MvPolynomial A k`. -/
@[simp]
theorem polynomialResolutionGenerator_zero (A : CommAlgCat.{max u v} k) (a : A) :
    polynomialResolutionGenerator.{u, v} k A 0 a = MvPolynomial.X a := rfl

/-- The polynomial generator in degree one.

For `p ∈ MvPolynomial A k`, the degree-one generator indexed by `p` is the variable `X_p` in
the next polynomial algebra. -/
@[simp]
theorem polynomialResolutionGenerator_one (A : CommAlgCat.{max u v} k)
    (p : MvPolynomial A k) :
    polynomialResolutionGenerator.{u, v} k A 1 p = MvPolynomial.X p := rfl

/-- Extensionality on polynomial resolution generators.

Two `k`-algebra maps from degree `n` of the polynomial resolution of `A` to an algebra `B` are
equal if they agree on every generator indexed by `T^n(A)`. -/
theorem polynomialResolution_hom_ext (A B : CommAlgCat.{max u v} k) (n : ℕ)
    (f g : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ⟶ B)
    (h : ∀ x : (polynomialPower.{u, v} k n).obj A,
      f.hom (polynomialResolutionGenerator.{u, v} k A n x) =
        g.hom (polynomialResolutionGenerator.{u, v} k A n x)) : f = g := by
  let e := polynomialResolutionObjIso.{u, v} k A n
  apply (cancel_epi e.inv).1
  apply CommAlgCat.hom_ext
  ext x
  exact h x

/-- Renaming of polynomial resolution generators.

For `f : A → B`, the degree-`n` resolution map sends the generator indexed by `x ∈ T^n(A)` to
the generator indexed by `T^n(f)(x)`. -/
theorem polynomialResolutionMap_generator {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) (x : (polynomialPower.{u, v} k n).obj A) :
    ((polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n))).hom
        (polynomialResolutionGenerator.{u, v} k A n x) =
      polynomialResolutionGenerator.{u, v} k B n
        (((polynomialPower.{u, v} k n).map f).hom x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A n
  let eB := polynomialResolutionObjIso.{u, v} k B n
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj B) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A n x))
    (polynomialResolutionObjIso_naturality.{u, v} k f n)
  change eB.hom.hom
      (((polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n))).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    MvPolynomial.rename (R := k) ((polynomialPower.{u, v} k n).map f).hom
      (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A n x)) at h
  rw [polynomialResolutionObjIso_hom_generator, MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n))).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k B n
      (((polynomialPower.{u, v} k n).map f).hom x))
  rw [polynomialResolutionObjIso_hom_generator]
  exact h

/-- Counit insertion under a successor polynomial comparison.

For `i : Fin (n+1)`, the counit insertion in `T^(n+2)(A)` at `i.castSucc` corresponds under
the polynomial comparisons to `T` applied to the counit insertion at `i` in `T^(n+1)(A)`. -/
@[reassoc]
theorem polynomialPower_epsilon_castSucc (n : ℕ) (i : Fin (n + 1))
    (A : CommAlgCat.{max u v} k) :
    Comonad.epsilonAtPos (polynomialComonad.{u, v} k) (n + 1) i.castSucc A ≫
        (polynomialPowerObjIso.{u, v} k n A).hom =
      (polynomialPowerObjIso.{u, v} k (n + 1) A).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.epsilonAtPos (polynomialComonad.{u, v} k) n i A) := by
  induction n generalizing A with
  | zero =>
    have hi : i = 0 := Fin.eq_zero (i : Fin 1)
    subst i
    exact polynomialPowerObjIso_naturality.{u, v} k 0
      ((polynomialComonad.{u, v} k).ε.app A)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      exact polynomialPowerObjIso_naturality.{u, v} k (n + 1)
        ((polynomialComonad.{u, v} k).ε.app A)
    | succ j =>
      exact ih (i := j) (A := (polynomialComonad.{u, v} k).obj A)

/-- Evaluation as the zeroth polynomial resolution face.

After identifying degree `n+1` with the polynomial algebra on degree `n`, the zeroth face is
evaluation of its variables at the corresponding elements of degree `n`. -/
@[reassoc]
theorem polynomialResolution_face_zero (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op =
      (polynomialPowerObjIso.{u, v} k (n + 1) A).hom ≫
        (polynomialComonad.{u, v} k).ε.app ((polynomialPower.{u, v} k (n + 1)).obj A) := by
  rw [polynomialResolution_map_δ]
  induction n generalizing A with
  | zero =>
    change (polynomialComonad.{u, v} k).ε.app ((polynomialComonad.{u, v} k).obj A) =
      𝟙 _ ≫ (polynomialComonad.{u, v} k).ε.app ((polynomialComonad.{u, v} k).obj A)
    exact (Category.id_comp _).symm
  | succ n ih =>
    exact ih ((polynomialComonad.{u, v} k).obj A)

/-- Renaming as a positive polynomial resolution face.

For `i : Fin (n+1)`, the face `d_(i+1)` corresponds under the degreewise polynomial
comparisons to `T` applied to the lower counit insertion indexed by `i`. -/
@[reassoc]
theorem polynomialResolution_face_succ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op ≫
        (polynomialResolutionObjIso.{u, v} k A n).hom =
      (polynomialResolutionObjIso.{u, v} k A (n + 1)).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A) := by
  rw [polynomialResolution_map_δ, polynomialResolutionObjIso_hom,
    polynomialResolutionObjIso_hom]
  change Comonad.epsilonAtPos (polynomialComonad.{u, v} k) (n + 1) i.succ.rev A ≫ _ =
    _ ≫ (polynomialComonad.{u, v} k).map
      (Comonad.epsilonAtPos (polynomialComonad.{u, v} k) n i.rev A)
  rw [Fin.rev_succ]
  exact polynomialPower_epsilon_castSucc.{u, v} k n i.rev A

/-- The zeroth face on a polynomial resolution generator.

For `x ∈ T^(n+1)(A)`, the zeroth face of the generator indexed by `x` in degree `n+1` is `x`
in degree `n`. -/
theorem polynomialResolution_face_zero_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op).hom
      (polynomialResolutionGenerator.{u, v} k A (n + 1) x) = x := by
  let e := polynomialResolutionObjIso.{u, v} k A (n + 1)
  have hd : (polynomialResolution.{u, v} k A).left.map
      (SimplexCategory.δ (0 : Fin (n + 2))).op =
      e.hom ≫ (polynomialComonad.{u, v} k).ε.app
        ((polynomialPower.{u, v} k (n + 1)).obj A) := by
    rw [polynomialResolutionObjIso_hom]
    exact polynomialResolution_face_zero.{u, v} k A n
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶
        (polynomialPower.{u, v} k (n + 1)).obj A =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) hd
  change _ = ((polynomialComonad.{u, v} k).ε.app
      ((polynomialPower.{u, v} k (n + 1)).obj A)).hom
    (e.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) at h
  rw [polynomialResolutionObjIso_hom_generator, polynomialComonad_counit_X] at h
  exact h

/-- A positive face on a polynomial resolution generator.

For `i : Fin (n+1)`, the face `d_(i+1)` sends the degree-`n+1` generator indexed by `x` to the
degree-`n` generator indexed by its lower counit-insertion image. -/
theorem polynomialResolution_face_succ_generator (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x) =
      polynomialResolutionGenerator.{u, v} k A n
        ((Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A (n + 1)
  let eB := polynomialResolutionObjIso.{u, v} k A n
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x))
    (polynomialResolution_face_succ.{u, v} k A i)
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    MvPolynomial.rename (R := k)
      (Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom
      (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) at h
  rw [polynomialResolutionObjIso_hom_generator, MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k A n
      ((Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom x))
  rw [polynomialResolutionObjIso_hom_generator]
  exact h

/-- Variable insertion as the zeroth polynomial degeneracy.

Under the degreewise polynomial comparisons, `s_0` is the comultiplication on the preceding
comonad power, followed by polynomial renaming through the inverse source comparison. -/
@[reassoc]
theorem polynomialResolution_degeneracy_zero (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op ≫
        (polynomialResolutionObjIso.{u, v} k A (n + 1)).hom =
      (polynomialResolutionObjIso.{u, v} k A n).hom ≫
        (polynomialComonad.{u, v} k).δ.app ((polynomialPower.{u, v} k n).obj A) ≫
          (polynomialComonad.{u, v} k).map (polynomialResolutionObjIso.{u, v} k A n).inv := by
  rw [polynomialResolution_map_σ, polynomialResolutionObjIso_hom,
    polynomialResolutionObjIso_hom, polynomialResolutionObjIso_inv]
  induction n generalizing A with
  | zero =>
    change (polynomialComonad.{u, v} k).δ.app A ≫ 𝟙 _ =
      𝟙 _ ≫ (polynomialComonad.{u, v} k).δ.app A ≫
        (polynomialComonad.{u, v} k).map (𝟙 _)
    rw [(polynomialComonad.{u, v} k).toFunctor.map_id]
    simp only [Category.id_comp, Category.comp_id]
    exact (Category.comp_id ((polynomialComonad.{u, v} k).δ.app A)).symm
  | succ n ih =>
    exact ih ((polynomialComonad.{u, v} k).obj A)

/-- Comultiplication insertion under a successor polynomial comparison.

For `i : Fin (n+1)`, comultiplication insertion in `T^(n+2)(A)` at `i.castSucc` corresponds
under the successor polynomial comparisons to `T` applied to the insertion at `i` in
`T^(n+1)(A)`. -/
@[reassoc]
theorem polynomialPower_delta_castSucc (n : ℕ) (i : Fin (n + 1))
    (A : CommAlgCat.{max u v} k) :
    Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 2) i.castSucc A ≫
        (polynomialPowerObjIso.{u, v} k (n + 2) A).hom =
      (polynomialPowerObjIso.{u, v} k (n + 1) A).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A) := by
  induction n generalizing A with
  | zero =>
    have hi : i = 0 := Fin.eq_zero (i : Fin 1)
    subst i
    exact polynomialPowerObjIso_naturality.{u, v} k 0
      ((polynomialComonad.{u, v} k).δ.app A)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      exact polynomialPowerObjIso_naturality.{u, v} k (n + 1)
        ((polynomialComonad.{u, v} k).δ.app A)
    | succ j =>
      exact ih (i := j) (A := (polynomialComonad.{u, v} k).obj A)

/-- Renaming as a positive polynomial resolution degeneracy.

For `i : Fin (n+1)`, the degeneracy `s_(i+1)` corresponds under the degreewise polynomial
comparisons to `T` applied to the lower comultiplication insertion indexed by `i`. -/
@[reassoc]
theorem polynomialResolution_degeneracy_succ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op ≫
        (polynomialResolutionObjIso.{u, v} k A (n + 2)).hom =
      (polynomialResolutionObjIso.{u, v} k A (n + 1)).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A) := by
  rw [polynomialResolution_map_σ, polynomialResolutionObjIso_hom,
    polynomialResolutionObjIso_hom]
  change Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 2) i.succ.rev A ≫ _ =
    _ ≫ (polynomialComonad.{u, v} k).map
      (Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 1) i.rev A)
  rw [Fin.rev_succ]
  exact polynomialPower_delta_castSucc.{u, v} k n i.rev A

/-- The zeroth degeneracy on a polynomial resolution generator.

For `x ∈ T^n(A)`, the zeroth degeneracy sends the degree-`n` generator indexed by `x` to the
degree-`n+1` generator indexed by that generator. -/
theorem polynomialResolution_degeneracy_zero_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k n).obj A) :
    ((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op).hom
      (polynomialResolutionGenerator.{u, v} k A n x) =
        polynomialResolutionGenerator.{u, v} k A (n + 1)
          (polynomialResolutionGenerator.{u, v} k A n x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A n
  let eB := polynomialResolutionObjIso.{u, v} k A (n + 1)
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k (n + 1)).obj A) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A n x))
    (polynomialResolution_degeneracy_zero.{u, v} k A n)
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    MvPolynomial.rename (R := k) eA.inv.hom
      (((polynomialComonad.{u, v} k).δ.app ((polynomialPower.{u, v} k n).obj A)).hom
        (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A n x))) at h
  rw [polynomialResolutionObjIso_hom_generator, polynomialComonad_comultiplication_X,
    MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1)
      (polynomialResolutionGenerator.{u, v} k A n x))
  have hindex : eA.inv.hom (MvPolynomial.X x) =
      polynomialResolutionGenerator.{u, v} k A n x := by
    dsimp only [eA, polynomialResolutionGenerator]
    rw [polynomialResolutionObjIso_inv]
    rfl
  have hright := polynomialResolutionObjIso_hom_generator.{u, v} k A (n + 1)
    (polynomialResolutionGenerator.{u, v} k A n x)
  exact h.trans
    ((congrArg (fun z : (polynomialPower.{u, v} k (n + 1)).obj A =>
      (MvPolynomial.X z : MvPolynomial ((polynomialPower.{u, v} k (n + 1)).obj A) k))
        hindex).trans hright.symm)

/-- A positive degeneracy on a polynomial resolution generator.

For `i : Fin (n+1)`, the degeneracy `s_(i+1)` sends a generator to the generator indexed by
its lower comultiplication-insertion image. -/
theorem polynomialResolution_degeneracy_succ_generator (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x) =
      polynomialResolutionGenerator.{u, v} k A (n + 2)
        ((Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A (n + 1)
  let eB := polynomialResolutionObjIso.{u, v} k A (n + 2)
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k (n + 2)).obj A) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x))
    (polynomialResolution_degeneracy_succ.{u, v} k A i)
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    MvPolynomial.rename (R := k)
      (Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom
      (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) at h
  rw [polynomialResolutionObjIso_hom_generator, MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 2)
      ((Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom x))
  rw [polynomialResolutionObjIso_hom_generator]
  exact h

/-- The augmentation on a degree-zero polynomial generator.

For `a ∈ A`, the degree-zero augmentation sends the generator `X_a` to `a`. -/
theorem polynomialResolution_augmentation_zero_generator (A : CommAlgCat.{max u v} k) (a : A) :
    ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk 0))).hom
      (polynomialResolutionGenerator.{u, v} k A 0 a) = a := by
  rw [polynomialResolutionGenerator_zero, polynomialResolution_augmentation_zero]
  exact polynomialComonad_counit_X.{u, v} k A a

/-- The augmentation on a higher polynomial generator.

For `x` in degree `n` of the polynomial resolution, augmenting the degree-`n+1` generator
indexed by `x` gives the degree-`n` augmentation of `x`. -/
theorem polynomialResolution_augmentation_succ_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk (n + 1)))).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x) =
      ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n))).hom x := by
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶ A =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x))
    (polynomialResolution_augmentation_naturality.{u, v} k A
      (SimplexCategory.δ (0 : Fin (n + 2))).op)
  change ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n))).hom
      (((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) = _ at h
  rw [polynomialResolution_face_zero_generator] at h
  exact h.symm

/-- Naturality of polynomial resolution augmentation in the algebra.

For `f : A → B`, the degree-`n` resolution map followed by augmentation to `B` equals
augmentation to `A` followed by `f`. -/
@[reassoc]
theorem polynomialResolutionMap_augmentation {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) :
    (polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n)) ≫
        (polynomialResolution.{u, v} k B).hom.app (op (SimplexCategory.mk n)) =
      (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n)) ≫ f := by
  have h : (polynomialResolutionMap.{u, v} k f).left ≫
      (polynomialResolution.{u, v} k B).hom =
    (polynomialResolution.{u, v} k A).hom ≫
      (SimplicialObject.const (CommAlgCat.{max u v} k)).map f :=
    (polynomialResolutionMap.{u, v} k f).w
  exact congrArg
    (fun t : (polynomialResolution.{u, v} k A).left ⟶
      (SimplicialObject.const (CommAlgCat.{max u v} k)).obj B =>
        t.app (op (SimplexCategory.mk n))) h

end CommAlgCat

end
