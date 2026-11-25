/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentWeightZero
public import MathlibExt.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Higher-form linearization of augmented algebras

For `P → A`, weight zero is `A ⊗[P] P`, and positive weight `n` is
`A ⊗[P] ⋀[P]^n Ω[P⁄k]`. Exterior base change identifies these modules with
exterior powers of the linearized cotangent object. Their maps are induced
by the given algebra maps and preserve differential words. Weight zero
agrees with the regular-module transport and weight one with the cotangent
functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Literal higher forms after the actual augmentation, including regular weight zero. -/
@[implicit_reducible]
def cotangentHigherLevel (n : ℕ) (P : Over A) : ModuleCat.{max u v} A :=
  match n with
  | 0 => cotangentWeightZeroLevel k A P
  | n + 1 =>
    letI : Algebra P.left A := cotangentAlgebra k A P
    ModuleCat.of A (A ⊗[P.left] (⋀[P.left]^(n + 1) (KaehlerDifferential k P.left)))

/-- Native scalar extension gives the actual exterior comparison, including its unit. -/
def cotangentHigherExteriorIso (n : ℕ) (P : Over A) :
    cotangentHigherLevel k A n P ≅
      (ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A n).obj
        (cotangent.{u, v} k A P) := by
  cases n with
  | zero =>
    exact cotangentWeightZeroLevelIso k A P ≪≫
      (exteriorPower.zeroEquiv A (cotangent k A P)).symm.toModuleIso
  | succ n =>
    letI : Algebra P.left A := cotangentAlgebra k A P
    exact (exteriorPower.baseChangeEquiv P.left A (KaehlerDifferential k P.left) (n + 1)).toModuleIso

/-- The actual operator, constructed from the existing original cotangent operator. -/
def cotangentHigherMap (n : ℕ) {P Q : Over A} (f : P ⟶ Q) :
    cotangentHigherLevel k A n P ⟶ cotangentHigherLevel k A n Q :=
  (cotangentHigherExteriorIso k A n P).hom ≫
    (ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A n).map (cotangentMap k A f) ≫
      (cotangentHigherExteriorIso k A n Q).inv

@[simp]
theorem cotangentHigherMap_id (n : ℕ) (P : Over A) :
    cotangentHigherMap k A n (𝟙 P) = 𝟙 (cotangentHigherLevel k A n P) := by
  let F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
    ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A n
  let e : cotangentHigherLevel.{u, v} k A n P ≅ F.obj (cotangent.{u, v} k A P) :=
    cotangentHigherExteriorIso.{u, v} k A n P
  have hId : F.map (𝟙 (cotangent.{u, v} k A P)) =
      𝟙 (F.obj (cotangent.{u, v} k A P)) := F.map_id _
  change e.hom ≫ F.map (cotangentMap.{u, v} k A (𝟙 P)) ≫ e.inv = _
  rw [cotangentMap_id.{u, v} k A P, hId, Category.id_comp]
  exact e.hom_inv_id

theorem cotangentHigherMap_comp (n : ℕ) {P Q T : Over A}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    cotangentHigherMap k A n (f ≫ g) =
      cotangentHigherMap k A n f ≫ cotangentHigherMap k A n g := by
  let F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
    ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A n
  let eP : cotangentHigherLevel.{u, v} k A n P ≅ F.obj (cotangent.{u, v} k A P) :=
    cotangentHigherExteriorIso.{u, v} k A n P
  let eQ : cotangentHigherLevel.{u, v} k A n Q ≅ F.obj (cotangent.{u, v} k A Q) :=
    cotangentHigherExteriorIso.{u, v} k A n Q
  let eT : cotangentHigherLevel.{u, v} k A n T ≅ F.obj (cotangent.{u, v} k A T) :=
    cotangentHigherExteriorIso.{u, v} k A n T
  let a : F.obj (cotangent.{u, v} k A P) ⟶ F.obj (cotangent.{u, v} k A Q) :=
    F.map (cotangentMap.{u, v} k A f)
  let b : F.obj (cotangent.{u, v} k A Q) ⟶ F.obj (cotangent.{u, v} k A T) :=
    F.map (cotangentMap.{u, v} k A g)
  have hComp : F.map (cotangentMap.{u, v} k A (f ≫ g)) = a ≫ b :=
    (congrArg F.map (cotangentMap_comp.{u, v} k A f g)).trans (F.map_comp _ _)
  change eP.hom ≫ F.map (cotangentMap.{u, v} k A (f ≫ g)) ≫ eT.inv =
    (eP.hom ≫ a ≫ eQ.inv) ≫ (eQ.hom ≫ b ≫ eT.inv)
  rw [hComp]
  calc
    eP.hom ≫ (a ≫ b) ≫ eT.inv = eP.hom ≫ a ≫ b ≫ eT.inv := by
      rw [Category.assoc]
    _ = eP.hom ≫ a ≫ (eQ.inv ≫ eQ.hom) ≫ b ≫ eT.inv := by
      rw [eQ.inv_hom_id, Category.id_comp]
    _ = (eP.hom ≫ a ≫ eQ.inv) ≫ (eQ.hom ≫ b ≫ eT.inv) := by
      simp only [Category.assoc]

/-- Higher-form linearization is functorial on the actual augmented algebras. -/
def cotangentHigherFunctor (n : ℕ) : Over A ⥤ ModuleCat.{max u v} A where
  obj := cotangentHigherLevel k A n
  map := cotangentHigherMap k A n
  map_id := cotangentHigherMap_id k A n
  map_comp := cotangentHigherMap_comp k A n

/-- The whole native exterior comparison is natural in the original augmented algebra. -/
def cotangentHigherExteriorNatIso (n : ℕ) :
    cotangentHigherFunctor k A n ≅
      cotangentFunctor.{u, v} k A ⋙
         ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A n :=
  NatIso.ofComponents (cotangentHigherExteriorIso k A n) (by
    intro P Q f
    let F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
      ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A n
    let eP : cotangentHigherLevel.{u, v} k A n P ≅ F.obj (cotangent.{u, v} k A P) :=
      cotangentHigherExteriorIso.{u, v} k A n P
    let eQ : cotangentHigherLevel.{u, v} k A n Q ≅ F.obj (cotangent.{u, v} k A Q) :=
      cotangentHigherExteriorIso.{u, v} k A n Q
    let a : F.obj (cotangent.{u, v} k A P) ⟶ F.obj (cotangent.{u, v} k A Q) :=
      F.map (cotangentMap.{u, v} k A f)
    change (eP.hom ≫ a ≫ eQ.inv) ≫ eQ.hom = eP.hom ≫ a
    calc
      (eP.hom ≫ a ≫ eQ.inv) ≫ eQ.hom =
          eP.hom ≫ a ≫ (eQ.inv ≫ eQ.hom) := by
        simp only [Category.assoc]
      _ = eP.hom ≫ a := by rw [eQ.inv_hom_id, Category.comp_id])

/-- An original positive-weight differential word in the literal coefficient tensor. -/
def cotangentHigherTensor (n : ℕ) (P : Over A) (a : A)
    (p : Fin (n + 1) → P.left) : cotangentHigherLevel k A (n + 1) P :=
  letI : Algebra P.left A := cotangentAlgebra k A P
  a ⊗ₜ[P.left] exteriorPower.ιMulti P.left (n + 1)
    (fun i => KaehlerDifferential.D k P.left (p i))

/-- The native exterior comparison retains each original differential and coefficient. -/
@[simp]
theorem cotangentHigherExteriorIso_tensor (n : ℕ) (P : Over A)
    (a : A) (p : Fin (n + 1) → P.left) :
    (cotangentHigherExteriorIso k A (n + 1) P).hom.hom
        (cotangentHigherTensor k A n P a p) =
      a • exteriorPower.ιMulti A (n + 1)
        (fun i => cotangentTensor k A P 1 (p i)) := by
  letI : Algebra P.left A := cotangentAlgebra k A P
  exact exteriorPower.baseChangeEquiv_apply_tmul_ιMulti
    P.left A (KaehlerDifferential k P.left) (n + 1) a
      (fun i => KaehlerDifferential.D k P.left (p i))

/-- Every positive-weight operator is the original algebra operator on differential words. -/
@[simp]
theorem cotangentHigherMap_tensor (n : ℕ) {P Q : Over A} (f : P ⟶ Q)
    (a : A) (p : Fin (n + 1) → P.left) :
    (cotangentHigherMap k A (n + 1) f).hom
        (cotangentHigherTensor k A n P a p) =
      cotangentHigherTensor k A n Q a (fun i => f.left.hom (p i)) := by
  let F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
    ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A (n + 1)
  let eP : cotangentHigherLevel.{u, v} k A (n + 1) P ≅
      F.obj (cotangent.{u, v} k A P) := cotangentHigherExteriorIso.{u, v} k A (n + 1) P
  let eQ : cotangentHigherLevel.{u, v} k A (n + 1) Q ≅
      F.obj (cotangent.{u, v} k A Q) := cotangentHigherExteriorIso.{u, v} k A (n + 1) Q
  let x : cotangentHigherLevel.{u, v} k A (n + 1) P := cotangentHigherTensor.{u, v} k A n P a p
  let y : cotangentHigherLevel.{u, v} k A (n + 1) Q :=
    cotangentHigherTensor.{u, v} k A n Q a (fun i => f.left.hom (p i))
  let l : F.obj (cotangent.{u, v} k A P) ⟶ F.obj (cotangent.{u, v} k A Q) :=
    F.map (cotangentMap.{u, v} k A f)
  apply (ModuleCat.mono_iff_injective eQ.hom).mp inferInstance
  change eQ.hom (eQ.inv (l (eP.hom x))) = eQ.hom y
  have hP : eP.hom x = a • exteriorPower.ιMulti A (n + 1)
      (fun i => cotangentTensor.{u, v} k A P 1 (p i)) :=
    cotangentHigherExteriorIso_tensor.{u, v} k A n P a p
  have hQ : eQ.hom y = a • exteriorPower.ιMulti A (n + 1)
      (fun i => cotangentTensor.{u, v} k A Q 1 (f.left.hom (p i))) :=
    cotangentHigherExteriorIso_tensor.{u, v} k A n Q a (fun i => f.left.hom (p i))
  have hWord : l (a • exteriorPower.ιMulti A (n + 1)
      (fun i => cotangentTensor.{u, v} k A P 1 (p i))) =
      a • exteriorPower.ιMulti A (n + 1)
        (fun i => cotangentTensor.{u, v} k A Q 1 (f.left.hom (p i))) := by
    let d : (⋀[A]^(n + 1) (cotangent.{u, v} k A P)) →ₗ[A]
        (⋀[A]^(n + 1) (cotangent.{u, v} k A Q)) :=
      exteriorPower.map (n + 1) (cotangentMap.{u, v} k A f).hom
    have hValue (z : ⋀[A]^(n + 1) (cotangent.{u, v} k A P)) : l z = d z := rfl
    have hMap : d (exteriorPower.ιMulti A (n + 1)
        (fun i => cotangentTensor.{u, v} k A P 1 (p i))) =
        exteriorPower.ιMulti A (n + 1)
          (fun i => (cotangentMap.{u, v} k A f).hom
            (cotangentTensor.{u, v} k A P 1 (p i))) :=
      exteriorPower.map_apply_ιMulti (cotangentMap.{u, v} k A f).hom _
    refine (hValue _).trans ((d.map_smul a _).trans ?_)
    refine (congrArg (fun z => a • z) hMap).trans ?_
    apply congrArg (fun z => a • exteriorPower.ιMulti A (n + 1) z)
    funext i
    exact cotangentMap_tensor.{u, v} k A f 1 (p i)
  exact (ModuleCat.hom_inv_apply eQ (l (eP.hom x))).trans
    ((congrArg l hP).trans (hWord.trans hQ.symm))

/-- The weight-zero operator is exactly the existing regular-module transport. -/
theorem cotangentHigherMap_zero_eq_weightZero {P Q : Over A} (f : P ⟶ Q) :
    cotangentHigherMap k A 0 f = cotangentWeightZeroTransport k A f := by
  let F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
    ModuleCat.exteriorPowerFunctorAt.{max u v, max u v} A 0
  let cP : cotangentHigherLevel.{u, v} k A 0 P ≅ F.obj (cotangent.{u, v} k A P) :=
    cotangentHigherExteriorIso.{u, v} k A 0 P
  let cQ : cotangentHigherLevel.{u, v} k A 0 Q ≅ F.obj (cotangent.{u, v} k A Q) :=
    cotangentHigherExteriorIso.{u, v} k A 0 Q
  let wP := cotangentWeightZeroLevelIso.{u, v} k A P
  let wQ := cotangentWeightZeroLevelIso.{u, v} k A Q
  let zP : F.obj (cotangent.{u, v} k A P) ≅ ModuleCat.of A A :=
    (exteriorPower.zeroEquiv A (cotangent.{u, v} k A P)).toModuleIso
  let zQ : F.obj (cotangent.{u, v} k A Q) ≅ ModuleCat.of A A :=
    (exteriorPower.zeroEquiv A (cotangent.{u, v} k A Q)).toModuleIso
  have hcP : cP.hom = wP.hom ≫ zP.inv := rfl
  have hcQ : cQ.inv = zQ.hom ≫ wQ.inv := rfl
  have hZero : F.map (cotangentMap.{u, v} k A f) ≫ zQ.hom = zP.hom :=
    ModuleCat.hom_ext (exteriorPower.zeroEquiv_naturality (cotangentMap.{u, v} k A f).hom)
  change cP.hom ≫ F.map (cotangentMap.{u, v} k A f) ≫ cQ.inv = wP.hom ≫ wQ.inv
  rw [hcP, hcQ]
  calc
    (wP.hom ≫ zP.inv) ≫ F.map (cotangentMap.{u, v} k A f) ≫ (zQ.hom ≫ wQ.inv) =
        wP.hom ≫ zP.inv ≫ (F.map (cotangentMap.{u, v} k A f) ≫ zQ.hom) ≫ wQ.inv := by
      simp only [Category.assoc]
    _ = wP.hom ≫ zP.inv ≫ zP.hom ≫ wQ.inv := by rw [hZero]
    _ = wP.hom ≫ wQ.inv := by rw [zP.inv_hom_id_assoc]

/-- The printed regular-module formula in weight zero, with the original algebra map. -/
@[simp]
theorem cotangentHigherMap_zero_tmul {P Q : Over A} (f : P ⟶ Q)
    (a : A) (p : P.left) :
    letI : Algebra P.left A := cotangentAlgebra k A P
    letI : Algebra Q.left A := cotangentAlgebra k A Q
    (cotangentHigherMap k A 0 f).hom (a ⊗ₜ[P.left] p) =
      a ⊗ₜ[Q.left] f.left.hom p := by
  rw [cotangentHigherMap_zero_eq_weightZero]
  exact cotangentWeightZeroTransport_tmul k A f a p

/-- Positive degree one is the existing actual cotangent functor. -/
def cotangentHigherOneNatIso :
    cotangentHigherFunctor k A 1 ≅ cotangentFunctor k A :=
  cotangentHigherExteriorNatIso k A 1 ≪≫
    isoWhiskerLeft (cotangentFunctor k A)
      (ModuleCat.exteriorPowerOneNatIso A) ≪≫ Functor.rightUnitor _

/-- The actual degree-one isomorphism sends the original coefficient word to a ⊗ dp. -/
@[simp]
theorem cotangentHigherOneNatIso_tensor (P : Over A) (a : A) (p : P.left) :
    ((cotangentHigherOneNatIso k A).hom.app P).hom
        (cotangentHigherTensor k A 0 P a (fun _ => p)) =
      cotangentTensor k A P a p := by
  change (exteriorPower.oneEquiv A (cotangent k A P))
    ((cotangentHigherExteriorIso k A 1 P).hom.hom _) = _
  rw [cotangentHigherExteriorIso_tensor, _root_.map_smul,
    exteriorPower.oneEquiv_ιMulti]
  letI : Algebra P.left A := cotangentAlgebra.{u, v} k A P
  change a • ((1 : A) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) =
    a ⊗ₜ[P.left] KaehlerDifferential.D k P.left p
  exact (TensorProduct.tmul_eq_smul_one_tmul (R := P.left)
    a (KaehlerDifferential.D k P.left p)).symm

/-- Maps out of an actual higher-form coefficient module are determined on exterior words.
The target module retains its independently specified original universe. -/
theorem cotangentHigher_hom_ext_succ (n : ℕ) (P : Over A)
    (M : ModuleCat.{t} A)
    {f g : (cotangentHigherLevel.{u, v} k A (n + 1) P) →ₗ[A] M}
    (h : letI : Algebra P.left A := cotangentAlgebra.{u, v} k A P
      letI : Module A (cotangentHigherLevel.{u, v} k A (n + 1) P) :=
        (cotangentHigherLevel.{u, v} k A (n + 1) P).isModule
      letI : Module A M := M.isModule
      ∀ (a : A) (ω : Fin (n + 1) → KaehlerDifferential k P.left),
        f (TensorProduct.tmul (R := P.left) (M := A)
          (N := ⋀[P.left]^(n + 1) (KaehlerDifferential k P.left)) a
            (exteriorPower.ιMulti P.left (n + 1) ω)) =
        g (TensorProduct.tmul (R := P.left) (M := A)
          (N := ⋀[P.left]^(n + 1) (KaehlerDifferential k P.left)) a
            (exteriorPower.ιMulti P.left (n + 1) ω))) : f = g := by
  letI : Algebra P.left A := cotangentAlgebra.{u, v} k A P
  letI : Module A M := M.isModule
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : IsScalarTower P.left A M := IsScalarTower.of_compHom P.left A M
  let f' : A ⊗[P.left] (⋀[P.left]^(n + 1) (KaehlerDifferential k P.left)) →ₗ[A] M := f
  let g' : A ⊗[P.left] (⋀[P.left]^(n + 1) (KaehlerDifferential k P.left)) →ₗ[A] M := g
  change f' = g'
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro a
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro ω
  exact h a ω

end CommAlgCat

end
