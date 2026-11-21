/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Zero-object-compatible Frobenius and Witt sheaf sources

The Frobenius operation uses `(p : R) = 0`, which also holds in the zero
ring of sections on an empty site object. A global `CharP R p` hypothesis
would exclude that object for prime `p`.

The tilted source is the actual native inverse limit of Frobenius.
Witt vectors and all coefficient restrictions use Mathlib's coefficientwise
ring homomorphism. Sheafification fixes the full ring-sheaf object.

References: Scholze, arXiv:1205.3463v2, Definition 6.1;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Definition 5.4.
Native Frobenius, Witt and sheaf operations are from Mathlib, Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafWittSource

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable (p : ℕ) [Fact p.Prime]

/-- Native pth-power Frobenius, including a zero coefficient ring. -/
def primeFrobenius (R : Type*) [CommRing R] (hp : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' x y := by
    classical
    by_cases hR : Nontrivial R
    · let := hR
      let : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      exact add_pow_char x y p
    · let : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      exact Subsingleton.elim _ _

@[simp] theorem primeFrobenius_apply (R : Type*) [CommRing R]
    (hp : (p : R) = 0) (x : R) : primeFrobenius p R hp x = x ^ p := rfl

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J CommRingCat.{1})

/-- Frobenius is fixed on every ring section and every original restriction. -/
def frobeniusSheaf (hp : ∀ U : Cᵒᵖ, (p : S.obj.obj U) = 0) : S ⟶ S :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (primeFrobenius p (S.obj.obj U) (hp U))
      naturality {U V} f := by
        ext x
        exact (map_pow (S.obj.map f).hom x p).symm }

/-- The source inverse tower has every iterate of the same native endomorphism. -/
abbrev inverseEndTower (e : End S) : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{1} where
  obj _ := S
  map {n m} f := (e ^ (n.unop - m.unop)).asHom
  map_id n := by simp
  map_comp {n m k} f g := by
    have hm : m.unop ≤ n.unop := leOfHom f.unop
    have hk : k.unop ≤ m.unop := leOfHom g.unop
    change (e ^ (n.unop - k.unop)).asHom =
      (e ^ (m.unop - k.unop) * e ^ (n.unop - m.unop)).asHom
    congr 1
    rw [← pow_add]
    congr 1
    omega

/-- Native shift on the complete Frobenius inverse system. -/
def inverseEndShift (e : End S) : limit (inverseEndTower S e) ⟶ limit (inverseEndTower S e) :=
  limit.lift (inverseEndTower S e)
    { pt := limit (inverseEndTower S e)
      π :=
        { app n := limit.π (inverseEndTower S e) (op (n.unop + 1))
          naturality {n m} f := by
            have h := limit.w (inverseEndTower S e)
              (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op
            simpa [inverseEndTower] using h.symm } }

@[reassoc (attr := simp)] theorem inverseEndShift_projection (e : End S) (n : ℕ) :
    inverseEndShift S e ≫ limit.π (inverseEndTower S e) (op n) =
      limit.π (inverseEndTower S e) (op (n + 1)) := by
  exact limit.lift_π _ _

abbrev tiltedSource (hp : ∀ U : Cᵒᵖ, (p : S.obj.obj U) = 0) :
    Sheaf J CommRingCat.{1} :=
  limit (inverseEndTower S (End.of (frobeniusSheaf p S hp)))

def tiltedProjection (hp : ∀ U : Cᵒᵖ, (p : S.obj.obj U) = 0) (n : ℕ) :
    tiltedSource p S hp ⟶ S :=
  limit.π (inverseEndTower S (End.of (frobeniusSheaf p S hp))) (op n)

/-- The raw Witt vectors and maps are the native coefficientwise construction. -/
def wittPresheaf : Cᵒᵖ ⥤ CommRingCat.{1} where
  obj U := CommRingCat.of (WittVector p (S.obj.obj U))
  map f := CommRingCat.ofHom (WittVector.map (p := p) (S.obj.map f).hom)
  map_id U := by
    ext x n
    simp
  map_comp f g := by
    ext x n
    simp

variable [HasSheafify J CommRingCat.{1}]

def wittSheaf : Sheaf J CommRingCat.{1} :=
  (presheafToSheaf J CommRingCat.{1}).obj (wittPresheaf p S)

end MathlibExt.CategoryTheory.SheafWittSource
