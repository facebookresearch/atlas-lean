/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DenominatorRootStacks

/-!
# Actual finite denominator powers and compatible root systems

For a sharp integral saturated monoid sheaf A, the denominator (1/n)A
is represented by the underlying sheaf A with embedding a↦a^n. The
injectivity proof uses sharpness and saturation in the actual groupification.
Transition from m-th to n-th roots for n|m uses the literal exponent m/n.

Compatible objects have actual roots at every positive exponent and
isomorphisms along these normalized transition functors, with unit and
composition equations. Their arrows are compatible actual root arrows;
the core is the groupoid 2-limit, rather than an unrelated limit carrier.

Source: Mattia Talpo and Angelo Vistoli, *Infinite root stacks and
quasi-coherent sheaves on logarithmic schemes*,
https://arxiv.org/abs/1410.1164v2, §§3--4; Theorem 5.24 and Theorem 6.16
are separate reconstruction/site-comparison endpoints.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteRootTowers
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.MonoidSheafCharts
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage

universe u

variable {X : Scheme.{u}}

/-- Saturation is computed in the actual Grothendieck group of local sections. -/
def IsSaturated (A : DeligneFaltingsSheaves.MonoidSheaf X) : Prop :=
  ∀ (U : X.Etale) (g : Algebra.GrothendieckGroup (A.obj.obj (op U))) (n : ℕ),
    0 < n → (∃ a : A.obj.obj (op U), Algebra.GrothendieckGroup.of a = g ^ n) →
      ∃ a : A.obj.obj (op U), Algebra.GrothendieckGroup.of a = g

/-- Coherent sharp charts with integral, saturated local sections. -/
def IsFineSaturated (A : DeligneFaltingsSheaves.MonoidSheaf X) : Prop :=
  IsCoherent A ∧
    (∀ U : X.Etale, Function.Injective
      (Algebra.GrothendieckGroup.of : A.obj.obj (op U) →* Algebra.GrothendieckGroup _)) ∧
    IsSaturated A

/-- The native power homomorphism on the actual sheaf of commutative monoids. -/
def powerMap (A : DeligneFaltingsSheaves.MonoidSheaf X) (n : ℕ) : A ⟶ A where
  hom :=
    { app := fun _U => CommMonCat.ofHom
        { toFun := fun a => a ^ n
          map_one' := one_pow n
          map_mul' := fun a b => mul_pow a b n }
      naturality := by intro U V f; ext a; exact (map_pow (A.obj.map f).hom a n).symm }

@[simp] theorem powerMap_apply (A : DeligneFaltingsSheaves.MonoidSheaf X) (n : ℕ)
    (U : X.Etale) (a : A.obj.obj (op U)) : (powerMap A n).hom.app (op U) a = a ^ n := rfl

@[simp] theorem powerMap_one (A : DeligneFaltingsSheaves.MonoidSheaf X) :
    powerMap A 1 = 𝟙 A := by ext U a; exact pow_one a

theorem powerMap_comp (A : DeligneFaltingsSheaves.MonoidSheaf X) (n m : ℕ) :
    powerMap A n ≫ powerMap A m = powerMap A (n*m) := by
  ext U a
  exact (pow_mul a n m).symm

/-- Sharpness is essential: saturation alone does not exclude torsion units. -/
theorem power_injective (A : DeligneFaltingsSheaves.MonoidSheaf X)
    (hA : IsFineSaturated A) (U : X.Etale) (n : ℕ) (hn : 0 < n) :
    Function.Injective (fun a : A.obj.obj (op U) => a ^ n) := by
  intro x y hxy
  change x ^ n = y ^ n at hxy
  let g : Algebra.GrothendieckGroup (A.obj.obj (op U)) :=
    Algebra.GrothendieckGroup.of x / Algebra.GrothendieckGroup.of y
  have hgn : g ^ n = 1 := by
    dsimp only [g]
    rw [div_pow, ← map_pow, ← map_pow, hxy]
    exact div_self' _
  obtain ⟨a, ha⟩ := hA.2.2 U g n hn ⟨1, by simp [hgn]⟩
  obtain ⟨b, hb⟩ := hA.2.2 U g⁻¹ n hn ⟨1, by simp [inv_pow, hgn]⟩
  have hab : a*b = 1 := hA.2.1 U (by rw [map_mul, ha, hb, mul_inv_cancel, map_one])
  have hau : IsUnit a := ⟨⟨a, b, hab, by simpa [mul_comm] using hab⟩, rfl⟩
  have haone : a = 1 := hA.1.1 U a hau
  have hg : g = 1 := ha.symm.trans (by rw [haone, map_one])
  exact hA.2.1 U (div_eq_one.mp hg)

/-- Positive powers form a genuine coherent Kummer denominator system. -/
def powerDenominator (A : DeligneFaltingsSheaves.MonoidSheaf X)
    (hA : IsFineSaturated A) (n : ℕ) (hn : 0 < n) : DenominatorSystem A A where
  map := powerMap A n
  kummer := ⟨fun U => power_injective A hA U n hn, by
    intro U b
    refine ⟨PUnit.{u+1}, fun _ => U, fun _ => 𝟙 U, ?_, ?_⟩
    · have htop : Sieve.ofArrows (fun _ : PUnit.{u+1} => U) (fun _ => 𝟙 U) = ⊤ := by
        ext V f
        simp only [Sieve.mem_ofArrows_iff, Sieve.top_apply, iff_true]
        exact ⟨PUnit.unit, f, (Category.comp_id f).symm⟩
      rw [htop]
      exact X.smallEtaleTopology.top_mem U
    · intro _i
      refine ⟨n, hn, b, ?_⟩
      change b ^ n = (A.obj.map (𝟙 (op U)) b) ^ n
      rw [mapIdentity]⟩
  coherentA := hA.1
  coherentB := hA.1

abbrev Exponent := {n : ℕ // 0 < n}

variable [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{u}) {A : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A)

abbrev FiniteRoots (T : Over X) (n : Exponent) := rootsAt I D (powerMap A n.val) T

theorem pulledPower_comp (T : Over X) (n m : Exponent) (h : n.val ∣ m.val) :
    (monoidPullback T.hom).map (powerMap A n.val) ≫
      (monoidPullback T.hom).map (powerMap A (m.val / n.val)) =
        (monoidPullback T.hom).map (powerMap A m.val) := by
  rw [← Functor.map_comp, powerMap_comp, Nat.mul_div_cancel' h]

/-- The actual m-th-to-n-th root restriction uses the literal exponent m/n. -/
structure RootRestriction (T : Over X) (n m : Exponent) (h : n.val ∣ m.val) where
  functor : FiniteRoots I D T m ⥤ FiniteRoots I D T n
  comparison : ∀ E : FiniteRoots I D T m,
    ComparisonAlong ((monoidPullback T.hom).map (powerMap A (m.val / n.val)))
      (functor.obj E).of.extended E.of.extended
  restriction : ∀ (E : FiniteRoots I D T m) (V : T.left.Etale)
      (a : (pulledMonoids T A).obj.obj (op V)),
    ((functor.obj E).of.restriction.comparison V a).hom ≫
      ((comparison E).comparison V
        (((monoidPullback T.hom).map (powerMap A n.val)).hom.app (op V) a)).hom =
    (E.of.restriction.comparison V a).hom ≫
      eqToHom (congrArg ((E.of.extended.chart V).module)
        ((ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op V))
          (pulledPower_comp T n m h)) a).symm))
  map_normalization : ∀ {E F : FiniteRoots I D T m} (f : E ⟶ F)
      (V : T.left.Etale) (b : (pulledMonoids T A).obj.obj (op V)),
    ((comparison E).comparison V b).hom ≫
      (f.iso.hom.hom.comparison V
        (((monoidPullback T.hom).map (powerMap A (m.val / n.val))).hom.app (op V) b)).hom =
    ((functor.map f).iso.hom.hom.comparison V b).hom ≫
      ((comparison F).comparison V b).hom

/-- A tower of actual roots with normalized power restrictions and coherent isomorphisms. -/
structure Tower (T : Over X) where
  transition : ∀ (n m : Exponent) (h : n.val ∣ m.val), RootRestriction I D T n m h
  identity : ∀ n : Exponent, (transition n n (dvd_refl _)).functor ≅ 𝟭 _
  composition : ∀ (n m k : Exponent) (h : n.val ∣ m.val) (h' : m.val ∣ k.val),
    (transition m k h').functor ⋙ (transition n m h).functor ≅
      (transition n k (dvd_trans h h')).functor
  left_unit : ∀ (n m : Exponent) (h : n.val ∣ m.val) (E : FiniteRoots I D T m),
    (composition n n m (dvd_refl _) h).hom.app E =
      (identity n).hom.app ((transition n m h).functor.obj E)
  right_unit : ∀ (n m : Exponent) (h : n.val ∣ m.val) (E : FiniteRoots I D T m),
    (composition n m m h (dvd_refl _)).hom.app E =
      (transition n m h).functor.map ((identity m).hom.app E)
  associativity : ∀ (n m k l : Exponent) (h : n.val ∣ m.val)
      (h' : m.val ∣ k.val) (h'' : k.val ∣ l.val) (E : FiniteRoots I D T l),
    (transition n m h).functor.map ((composition m k l h' h'').hom.app E) ≫
      (composition n m l h (dvd_trans h' h'')).hom.app E =
    (composition n m k h h').hom.app ((transition k l h'').functor.obj E) ≫
      (composition n k l (dvd_trans h h') h'').hom.app E

/-- Actual objects in the groupoid 2-limit of a normalized finite root tower. -/
structure CompatibleRoot {T : Over X} (R : Tower I D T) where
  root : ∀ n : Exponent, FiniteRoots I D T n
  comparison : ∀ (n m : Exponent) (h : n.val ∣ m.val),
    root n ≅ (R.transition n m h).functor.obj (root m)
  identity : ∀ n : Exponent,
    (comparison n n (dvd_refl _)).hom ≫ (R.identity n).hom.app (root n) = 𝟙 (root n)
  composition : ∀ (n m k : Exponent) (h : n.val ∣ m.val) (h' : m.val ∣ k.val),
    (comparison n m h).hom ≫
      (R.transition n m h).functor.map (comparison m k h').hom ≫
      (R.composition n m k h h').hom.app (root k) =
        (comparison n k (dvd_trans h h')).hom

namespace CompatibleRoot
variable {I D} {T : Over X} {R : Tower I D T}

structure Hom (E F : CompatibleRoot I D R) where
  component : ∀ n : Exponent, E.root n ⟶ F.root n
  naturality : ∀ (n m : Exponent) (h : n.val ∣ m.val),
    component n ≫ (F.comparison n m h).hom =
      (E.comparison n m h).hom ≫ (R.transition n m h).functor.map (component m)

@[ext] theorem Hom.ext {E F : CompatibleRoot I D R} {f g : Hom E F}
    (h : ∀ n, f.component n = g.component n) : f = g := by
  cases f; cases g; congr; exact funext h

instance : Category (CompatibleRoot I D R) where
  Hom := Hom
  id E := ⟨fun n => 𝟙 (E.root n), by intro n m h; simp⟩
  comp f g := ⟨fun n => f.component n ≫ g.component n, by
    intro n m h
    rw [Category.assoc, g.naturality, ← Category.assoc, f.naturality,
      Category.assoc, ← Functor.map_comp]⟩
  id_comp f := by apply Hom.ext; intro n; exact Category.id_comp _
  comp_id f := by apply Hom.ext; intro n; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; intro n; exact Category.assoc _ _ _

/-- Coordinatewise inverses preserve every actual root-transition square. -/
def Hom.inverse {E F : CompatibleRoot I D R} (f : E ⟶ F) : F ⟶ E where
  component n := inv (f.component n)
  naturality n m h := by
    apply (cancel_epi (f.component n)).mp
    rw [IsIso.hom_inv_id_assoc, ← Category.assoc, f.naturality,
      Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]

instance : IsGroupoid (CompatibleRoot I D R) where
  all_isIso f := ⟨⟨Hom.inverse f, by
    apply Hom.ext; intro n
    change f.component n ≫ inv (f.component n) = 𝟙 _
    exact IsIso.hom_inv_id _, by
    apply Hom.ext; intro n
    change inv (f.component n) ≫ f.component n = 𝟙 _
    exact IsIso.inv_hom_id _⟩⟩

/-- The literal component projection of a compatible root system. -/
def evaluation (n : Exponent) : CompatibleRoot I D R ⥤ FiniteRoots I D T n where
  obj E := E.root n
  map f := f.component n

end CompatibleRoot

/-- The actual groupoid of compatible root systems. -/
abbrev InfiniteRoots {T : Over X} (R : Tower I D T) := Core (CompatibleRoot I D R)

end MathlibExt.AlgebraicGeometry.FiniteRootTowers
