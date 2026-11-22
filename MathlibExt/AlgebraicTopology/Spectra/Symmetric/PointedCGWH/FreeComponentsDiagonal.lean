/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- The equal-degree comparison reuses the accepted native trivial-complement API
-- and the original sphere free/evaluation component comparison.
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeComponentsFunctor
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereSequence
import MathlibExt.Topology.Category.PointedCGWH.TrivialCoinvariants

/-!
# Diagonal components of free symmetric spectra

At equal source and target degrees, the balanced induction coefficient reduces to
the degree-zero coefficient with a copy for each automorphism of the finite cardinal.
For the sphere sequence, the degree-zero coefficient is the smash unit, giving a
natural comparison with the smash product of the coefficient and the based automorphism set.
The comparisons respect quotient generators, coefficient maps, and the target group action.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid

namespace CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual automorphism group of the empty cardinal is subsingleton. -/
theorem cardZeroAutSubsingleton : Subsingleton (Aut (card 0)) := by
  let e := finAutEquiv (card 0)
  refine ⟨fun a b => e.injective ?_⟩
  apply Equiv.ext
  intro i
  exact Fin.elim0 i

end CategoryTheory.Operad.SmallFinBijGroupoid

namespace PointedCGWH

/-- The actual degree-zero sphere coefficient is the selected native smash unit. -/
def sphereSequenceZeroIso :
    sphereSequence.{u, v}.functor.obj (card 0) ≅ 𝟙_ PointedCGWH.{u, v} :=
  eqToIso ((sphereSequence_obj (card 0)).trans
    (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_zero sphereOne))

/-- Tensor the original zero sphere coefficient with X, then use the native left unitor. -/
def sphereSequenceZeroCoefficientIso (X : PointedCGWH.{u, v}) :
    sphereSequence.{u, v}.functor.obj (card 0) ⊗ X ≅ X :=
  (tensorRight X).mapIso sphereSequenceZeroIso ≪≫ λ_ X

/-- The actual sphere-zero coefficient comparison is natural for every coefficient map. -/
theorem sphereSequenceZeroCoefficientIso_naturality
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (𝟙 (sphereSequence.functor.obj (card 0)) ⊗ₘ f) ≫
        (sphereSequenceZeroCoefficientIso Y).hom =
      (sphereSequenceZeroCoefficientIso X).hom ≫ f := by
  let A0 := sphereSequence.{u, v}.functor.obj (card 0)
  let U := 𝟙_ PointedCGWH.{u, v}
  let p : A0 ≅ U := sphereSequenceZeroIso
  have hs : (𝟙 A0 ⊗ₘ f) ≫ (p.hom ▷ Y) =
      (p.hom ▷ X) ≫ (𝟙 U ⊗ₘ f) := by
    simpa only [id_tensorHom] using whisker_exchange p.hom f
  have hu : (𝟙 U ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f :=
    (congrArg (fun g => g ≫ (λ_ Y).hom) (id_tensorHom U f)).trans
      (leftUnitor_naturality f)
  change (𝟙 A0 ⊗ₘ f) ≫ (p.hom ▷ Y ≫ (λ_ Y).hom) =
    (p.hom ▷ X ≫ (λ_ X).hom) ≫ f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (λ_ Y).hom) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (p.hom ▷ X) ≫ g) hu).trans (Category.assoc _ _ _).symm)))

/-- The original diagonal complement reduces to zero by its actual cardinal equality. -/
def sphereSequenceDiagonalCoefficientIso (n : ℕ) (X : PointedCGWH.{u, v}) :
    sphereSequence.{u, v}.functor.obj (card (n - n)) ⊗ X ≅ X :=
  (tensorRight X).mapIso
      (eqToIso (congrArg (fun r => sphereSequence.{u, v}.functor.obj (card r))
        (Nat.sub_self n))) ≪≫
    sphereSequenceZeroCoefficientIso X

/-- The actual cardinal transport and native unit comparison retain coefficient naturality. -/
theorem sphereSequenceDiagonalCoefficientIso_naturality
    (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (𝟙 (sphereSequence.functor.obj (card (n - n))) ⊗ₘ f) ≫
        (sphereSequenceDiagonalCoefficientIso n Y).hom =
      (sphereSequenceDiagonalCoefficientIso n X).hom ≫ f := by
  let R := sphereSequence.{u, v}.functor.obj (card (n - n))
  let A0 := sphereSequence.{u, v}.functor.obj (card 0)
  let p : R ≅ A0 := eqToIso
    (congrArg (fun r => sphereSequence.{u, v}.functor.obj (card r)) (Nat.sub_self n))
  let cX := sphereSequenceZeroCoefficientIso X
  let cY := sphereSequenceZeroCoefficientIso Y
  have hs : (𝟙 R ⊗ₘ f) ≫ (p.hom ▷ Y) =
      (p.hom ▷ X) ≫ (𝟙 A0 ⊗ₘ f) := by
    simpa only [id_tensorHom] using whisker_exchange p.hom f
  have hu : (𝟙 A0 ⊗ₘ f) ≫ cY.hom = cX.hom ≫ f :=
    sphereSequenceZeroCoefficientIso_naturality f
  change (𝟙 R ⊗ₘ f) ≫ (p.hom ▷ Y ≫ cY.hom) = (p.hom ▷ X ≫ cX.hom) ≫ f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ cY.hom) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (p.hom ▷ X) ≫ g) hu).trans (Category.assoc _ _ _).symm)))

/-- The general equal-degree component retains its actual degree-zero coefficient. -/
def nativeCardInducedDiagonalIso
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    (n : ℕ) (X : PointedCGWH.{u, v}) :
    (nativeCardInducedFunctor A (Nat.le_refl n)).obj X ≅
      discreteSmashObj.{u, v, 0} (Aut (card n)) (A.functor.obj (card (n - n)) ⊗ X) := by
  let R := card (n - n)
  let N := card n
  let Z := A.functor.obj R ⊗ X
  let rho := blockCoefficientAction A R X
  let iota := blockAutHom R N N (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))
  letI : Subsingleton (Aut R) := by
    simpa only [R, Nat.sub_self] using cardZeroAutSubsingleton
  exact nativeBalancedTrivialIso.{u, v, 0, 0} (Aut R) (Aut N) Z rho iota

/-- Every original native quotient generator remains the corresponding discrete injection. -/
theorem nativeCardInducedDiagonalIso_generator
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    (n : ℕ) (X : PointedCGWH.{u, v}) (g : Aut (card n)) :
    nativeBalancedGenerator.{u, v, 0, 0}
        (Aut (card (n - n))) (Aut (card n)) (A.functor.obj (card (n - n)) ⊗ X)
        (blockCoefficientAction A (card (n - n)) X)
        (blockAutHom (card (n - n)) (card n) (card n)
          (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) g ≫
      (nativeCardInducedDiagonalIso A n X).hom =
    discreteSmashIncl.{u, v, 0} (Aut (card n)) (A.functor.obj (card (n - n)) ⊗ X) g := by
  let R := card (n - n)
  let N := card n
  let : Subsingleton (Aut R) := by
    simpa only [R, Nat.sub_self] using cardZeroAutSubsingleton
  exact nativeBalancedTrivialIso_generator.{u, v, 0, 0}
    (Aut R) (Aut N) (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
    (blockAutHom R N N (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) g

/-- Coefficient maps retain the same actual equal-degree quotient comparison. -/
theorem nativeCardInducedDiagonalIso_naturality
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (nativeCardInducedFunctor A (Nat.le_refl n)).map f ≫
        (nativeCardInducedDiagonalIso A n Y).hom =
      (nativeCardInducedDiagonalIso A n X).hom ≫
        nativeSmashCoefficientMap.{u, v, 0} (Aut (card n))
          (A.functor.obj (card (n - n)) ⊗ X) (A.functor.obj (card (n - n)) ⊗ Y)
          (𝟙 (A.functor.obj (card (n - n))) ⊗ₘ f) := by
  let R := card (n - n)
  let N := card n
  let : Subsingleton (Aut R) := by
    simpa only [R, Nat.sub_self] using cardZeroAutSubsingleton
  exact nativeBalancedTrivialIso_naturality.{u, v, 0, 0}
    (Aut R) (Aut N) (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
    (blockAutHom R N N (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n))))
    (A.functor.obj R ⊗ Y) (blockCoefficientAction A R Y)
    (𝟙 (A.functor.obj R) ⊗ₘ f) (blockCoefficientAction_naturality A R f)

/-- The equal-degree comparison retains the full original target left action. -/
theorem nativeCardInducedDiagonalIso_left
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    (n : ℕ) (X : PointedCGWH.{u, v}) (k : Aut (card n)) :
    (nativeBalancedLeftAut.{u, v, 0, 0}
        (Aut (card (n - n))) (Aut (card n)) (A.functor.obj (card (n - n)) ⊗ X)
        (blockCoefficientAction A (card (n - n)) X)
        (blockAutHom (card (n - n)) (card n) (card n)
          (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) k).asIso.hom ≫
      (nativeCardInducedDiagonalIso A n X).hom =
    (nativeCardInducedDiagonalIso A n X).hom ≫
      discreteSmashLeft.{u, v, 0} (Aut (card n)) (A.functor.obj (card (n - n)) ⊗ X) k := by
  let R := card (n - n)
  let N := card n
  let : Subsingleton (Aut R) := by
    simpa only [R, Nat.sub_self] using cardZeroAutSubsingleton
  exact nativeBalancedTrivialIso_left.{u, v, 0, 0}
    (Aut R) (Aut N) (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
    (blockAutHom R N N (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) k

/-- The sphere coefficient reduces through the actual tensor unit to G-plus smash X. -/
def nativeSphereCardInducedDiagonalIso (n : ℕ) (X : PointedCGWH.{u, v}) :
    (nativeCardInducedFunctor sphereSequence (Nat.le_refl n)).obj X ≅
      discreteSmashObj.{u, v, 0} (Aut (card n)) X :=
  nativeCardInducedDiagonalIso sphereSequence n X ≪≫
    (tensorLeft (basedDiscreteObj.{u, v, 0} (Aut (card n)))).mapIso
      (sphereSequenceDiagonalCoefficientIso n X)

/-- The coefficient-unit comparison acts on each original native quotient generator. -/
theorem nativeSphereCardInducedDiagonalIso_generator
    (n : ℕ) (X : PointedCGWH.{u, v}) (g : Aut (card n)) :
    nativeBalancedGenerator.{u, v, 0, 0}
        (Aut (card (n - n))) (Aut (card n))
        (sphereSequence.functor.obj (card (n - n)) ⊗ X)
        (blockCoefficientAction sphereSequence (card (n - n)) X)
        (blockAutHom (card (n - n)) (card n) (card n)
          (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) g ≫
      (nativeSphereCardInducedDiagonalIso n X).hom =
    (sphereSequenceDiagonalCoefficientIso n X).hom ≫
      discreteSmashIncl.{u, v, 0} (Aut (card n)) X g := by
  let Z := sphereSequence.{u, v}.functor.obj (card (n - n)) ⊗ X
  let B := basedDiscreteObj.{u, v, 0} (Aut (card n))
  let e := nativeCardInducedDiagonalIso sphereSequence n X
  let c := sphereSequenceDiagonalCoefficientIso n X
  let qg := nativeBalancedGenerator.{u, v, 0, 0}
    (Aut (card (n - n))) (Aut (card n))
    (sphereSequence.functor.obj (card (n - n)) ⊗ X)
    (blockCoefficientAction sphereSequence (card (n - n)) X)
    (blockAutHom (card (n - n)) (card n) (card n)
      (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) g
  let jg : Z ⟶ B ⊗ Z := discreteSmashIncl.{u, v, 0} (Aut (card n)) Z g
  have hq : qg ≫ e.hom = jg := nativeCardInducedDiagonalIso_generator sphereSequence n X g
  have hmap : (tensorLeft B).map c.hom =
      nativeSmashCoefficientMap.{u, v, 0} (Aut (card n)) Z X c.hom :=
    (id_tensorHom B c.hom).symm
  have hj : jg ≫ nativeSmashCoefficientMap.{u, v, 0} (Aut (card n)) Z X c.hom =
      c.hom ≫ discreteSmashIncl.{u, v, 0} (Aut (card n)) X g :=
    nativeSmashCoefficientMap_generator.{u, v, 0} (Aut (card n)) Z X c.hom g
  change qg ≫ (e.hom ≫ (tensorLeft B).map c.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (tensorLeft B).map c.hom) hq).trans
      ((congrArg (fun f => jg ≫ f) hmap).trans hj))

/-- The original equal-degree sphere comparison is natural in every coefficient map. -/
theorem nativeSphereCardInducedDiagonalIso_naturality
    (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (nativeCardInducedFunctor sphereSequence (Nat.le_refl n)).map f ≫
        (nativeSphereCardInducedDiagonalIso n Y).hom =
      (nativeSphereCardInducedDiagonalIso n X).hom ≫
        nativeSmashCoefficientMap.{u, v, 0} (Aut (card n)) X Y f := by
  let R := card (n - n)
  let N := card n
  let S := sphereSequence.{u, v}
  let W := S.functor.obj R
  let F := nativeCardInducedFunctor S (Nat.le_refl n)
  let iota := blockAutHom R N N (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))
  apply nativeBalanced_hom_ext.{u, v, 0, 0}
    (Aut R) (Aut N) (W ⊗ X) (blockCoefficientAction S R X) iota
  intro g
  let qX := nativeBalancedGenerator.{u, v, 0, 0}
    (Aut R) (Aut N) (W ⊗ X) (blockCoefficientAction S R X) iota g
  let qY := nativeBalancedGenerator.{u, v, 0, 0}
    (Aut R) (Aut N) (W ⊗ Y) (blockCoefficientAction S R Y) iota g
  let eX := nativeSphereCardInducedDiagonalIso n X
  let eY := nativeSphereCardInducedDiagonalIso n Y
  let cX := sphereSequenceDiagonalCoefficientIso n X
  let cY := sphereSequenceDiagonalCoefficientIso n Y
  let jX := discreteSmashIncl.{u, v, 0} (Aut N) X g
  let jY := discreteSmashIncl.{u, v, 0} (Aut N) Y g
  let t := 𝟙 W ⊗ₘ f
  let m := nativeSmashCoefficientMap.{u, v, 0} (Aut N) X Y f
  have hm : qX ≫ F.map f = t ≫ qY :=
    nativeBalancedMap_generator.{u, v, 0, 0}
      (Aut R) (Aut N) (W ⊗ X) (blockCoefficientAction S R X) iota
      (W ⊗ Y) (blockCoefficientAction S R Y) t
      (blockCoefficientAction_naturality S R f) g
  have heX : qX ≫ eX.hom = cX.hom ≫ jX :=
    nativeSphereCardInducedDiagonalIso_generator n X g
  have heY : qY ≫ eY.hom = cY.hom ≫ jY :=
    nativeSphereCardInducedDiagonalIso_generator n Y g
  have hc : t ≫ cY.hom = cX.hom ≫ f :=
    sphereSequenceDiagonalCoefficientIso_naturality n f
  have hj : jX ≫ m = f ≫ jY :=
    nativeSmashCoefficientMap_generator.{u, v, 0} (Aut N) X Y f g
  have hLeft : (qX ≫ F.map f) ≫ eY.hom = cX.hom ≫ f ≫ jY := by
    calc
      _ = (t ≫ qY) ≫ eY.hom := congrArg (fun a => a ≫ eY.hom) hm
      _ = t ≫ (qY ≫ eY.hom) := Category.assoc _ _ _
      _ = t ≫ (cY.hom ≫ jY) := congrArg (fun a => t ≫ a) heY
      _ = (t ≫ cY.hom) ≫ jY := (Category.assoc _ _ _).symm
      _ = (cX.hom ≫ f) ≫ jY := congrArg (fun a => a ≫ jY) hc
      _ = cX.hom ≫ f ≫ jY := Category.assoc _ _ _
  have hRight : (qX ≫ eX.hom) ≫ m = cX.hom ≫ f ≫ jY := by
    calc
      _ = (cX.hom ≫ jX) ≫ m := congrArg (fun a => a ≫ m) heX
      _ = cX.hom ≫ (jX ≫ m) := Category.assoc _ _ _
      _ = cX.hom ≫ f ≫ jY := congrArg (fun a => cX.hom ≫ a) hj
  change qX ≫ (F.map f ≫ eY.hom) = qX ≫ (eX.hom ≫ m)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

/-- The actual sphere-unit comparison retains the full target multiplication. -/
theorem nativeSphereCardInducedDiagonalIso_left
    (n : ℕ) (X : PointedCGWH.{u, v}) (k : Aut (card n)) :
    (nativeBalancedLeftAut.{u, v, 0, 0}
        (Aut (card (n - n))) (Aut (card n))
        (sphereSequence.functor.obj (card (n - n)) ⊗ X)
        (blockCoefficientAction sphereSequence (card (n - n)) X)
        (blockAutHom (card (n - n)) (card n) (card n)
          (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))) k).asIso.hom ≫
      (nativeSphereCardInducedDiagonalIso n X).hom =
    (nativeSphereCardInducedDiagonalIso n X).hom ≫
      discreteSmashLeft.{u, v, 0} (Aut (card n)) X k := by
  let R := card (n - n)
  let N := card n
  let S := sphereSequence.{u, v}
  let Z := S.functor.obj R ⊗ X
  let rho := blockCoefficientAction S R X
  let iota := blockAutHom R N N (cardBlockSumIso (Nat.sub_add_cancel (Nat.le_refl n)))
  apply nativeBalanced_hom_ext.{u, v, 0, 0} (Aut R) (Aut N) Z rho iota
  intro g
  let qg := nativeBalancedGenerator.{u, v, 0, 0} (Aut R) (Aut N) Z rho iota g
  let qkg := nativeBalancedGenerator.{u, v, 0, 0} (Aut R) (Aut N) Z rho iota (k * g)
  let a := (nativeBalancedLeftAut.{u, v, 0, 0} (Aut R) (Aut N) Z rho iota k).asIso.hom
  let e := nativeSphereCardInducedDiagonalIso n X
  let c := sphereSequenceDiagonalCoefficientIso n X
  let jg := discreteSmashIncl.{u, v, 0} (Aut N) X g
  let jkg := discreteSmashIncl.{u, v, 0} (Aut N) X (k * g)
  let l := discreteSmashLeft.{u, v, 0} (Aut N) X k
  have ha : qg ≫ a = qkg :=
    nativeBalancedLeftAut_generator.{u, v, 0, 0} (Aut R) (Aut N) Z rho iota k g
  have he : qg ≫ e.hom = c.hom ≫ jg :=
    nativeSphereCardInducedDiagonalIso_generator n X g
  have hek : qkg ≫ e.hom = c.hom ≫ jkg :=
    nativeSphereCardInducedDiagonalIso_generator n X (k * g)
  have hl : jg ≫ l = jkg := discreteSmashLeft_generator.{u, v, 0} (Aut N) X k g
  have hLeft : (qg ≫ a) ≫ e.hom = c.hom ≫ jkg :=
    (congrArg (fun f => f ≫ e.hom) ha).trans hek
  have hRight : (qg ≫ e.hom) ≫ l = c.hom ≫ jkg :=
    (congrArg (fun f => f ≫ l) he).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f => c.hom ≫ f) hl))
  change qg ≫ (a ≫ e.hom) = qg ≫ (e.hom ≫ l)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

/-- These actual equal-degree sphere comparisons form a natural isomorphism. -/
def nativeSphereCardInducedDiagonalNatIso (n : ℕ) :
    nativeCardInducedFunctor sphereSequence.{u, v} (Nat.le_refl n) ≅
      tensorLeft (basedDiscreteObj.{u, v, 0} (Aut (card n))) :=
  NatIso.ofComponents (fun X => nativeSphereCardInducedDiagonalIso n X)
    (by
      intro X Y f
      have hn := nativeSphereCardInducedDiagonalIso_naturality n f
      exact hn.trans (congrArg
        (fun m => (nativeSphereCardInducedDiagonalIso n X).hom ≫ m)
        (id_tensorHom (basedDiscreteObj.{u, v, 0} (Aut (card n))) f)))

/-- The same original sphere free/evaluation component is the actual G-plus smash functor. -/
def nativeSphereFreeAtCardDiagonalIso (n : ℕ) :
    Mod.dayFreeAt sphereSequenceCommMon.{u, v}.X (card n) ⋙
        Mod.dayEvaluation sphereSequenceCommMon.{u, v}.X (card n) ≅
      tensorLeft (basedDiscreteObj.{u, v, 0} (Aut (card n))) :=
  dayFreeAtCardNativeIso sphereSequenceCommMon.{u, v}.X (Nat.le_refl n) ≪≫
    nativeSphereCardInducedDiagonalNatIso n

end PointedCGWH
