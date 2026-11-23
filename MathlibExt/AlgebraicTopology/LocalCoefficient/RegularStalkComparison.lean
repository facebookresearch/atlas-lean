/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarChangeOfCategory
public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# The actual integral stalk tensor functor at independent carrier universes

This construction uses the stock underlying representation tensor,
intertwining maps, curry/uncurry proof and coinvariant functor. Its scalar is
literally ℤ. The stalk and deck-group universes are independent of that scalar;
no replacement integer ring or monoidal tensor-unit assumption is used.

Coproduct preservation is derived from the actual tensor-Hom adjunction.
The chain comparison maps only a derived bounded-projective homotopy
equivalence; it does not assume that tensor preserves quasi-isomorphisms.
The later coefficient-map square and acyclic-fiber criterion use these same maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped MonoidAlgebra TensorProduct

universe u v

namespace ActualIntegerStalkTensor

-- Prefer the existing structural module on tensors and linear maps over
-- the competing canonical integer action; all remain the SAME ℤ-modules.
attribute [local instance 1001] TensorProduct.instModule LinearMap.module


local instance (Γ : Type v) [Group Γ] (I : Type u) :
    HasColimitsOfShape (Discrete I) (Rep.{u} ℤ Γ) := inferInstance

local instance (Γ : Type v) [Group Γ] : HasCoproducts.{u} (Rep.{u} ℤ Γ) :=
  fun _I => inferInstance


variable {Γ : Type v} [Group Γ]

local instance (M : Type*) [AddCommGroup M] : SMulCommClass ℤ ℤ M where
  smul_comm r s m := by
    rw [← mul_smul, ← mul_smul, Int.mul_comm]

/-- The stock tensor maps, bundled without a same-universe tensor unit. -/
private noncomputable def tensorLeft (A : Rep.{u} ℤ Γ) :
    Rep.{u} ℤ Γ ⥤ Rep.{u} ℤ Γ where
  obj B := by
    letI : AddCommGroup (A ⊗[ℤ] B) := TensorProduct.addCommGroup
    letI : Module ℤ (A ⊗[ℤ] B) := TensorProduct.instModule
    exact Rep.of (A.ρ.tprod B.ρ)
  map {B C} f := by
    letI : AddCommGroup (A ⊗[ℤ] B) := TensorProduct.addCommGroup
    letI : AddCommGroup (A ⊗[ℤ] C) := TensorProduct.addCommGroup
    letI : Module ℤ (A ⊗[ℤ] B) := TensorProduct.instModule
    letI : Module ℤ (A ⊗[ℤ] C) := TensorProduct.instModule
    exact Rep.ofHom (f.hom.lTensor A.ρ)
  map_id B := by
    apply Rep.hom_ext
    exact Representation.IntertwiningMap.lTensor_id
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact TensorProduct.ext' (fun a b => rfl)

/-- Additivity is the existing underlying tensor-additivity equation. -/
private instance tensorLeft_additive (A : Rep.{u} ℤ Γ) : (tensorLeft A).Additive where
  map_add {X Y} f g := by
    apply Rep.hom_ext
    change Representation.IntertwiningMap.lTensor A.ρ (f.hom + g.hom) =
      Representation.IntertwiningMap.lTensor A.ρ f.hom +
        Representation.IntertwiningMap.lTensor A.ρ g.hom
    exact Representation.IntertwiningMap.lTensor_add _ _

/-- The same stock curry/uncurry argument at the actual stalk universe. -/
private noncomputable def tensorHomEquiv (A B C : Rep.{u} ℤ Γ) :
    ((tensorLeft A).obj B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := by
    let H : Rep.{u} ℤ Γ := (Rep.ihom A).obj C
    letI : AddCommGroup H := H.hV1
    letI : Module ℤ H := H.hV2
    letI : Module ℤ C := C.hV2
    letI : MulAction ℤ C := C.hV2.toDistribMulAction.toMulAction
    letI : SMul ℤ C := C.hV2.toDistribMulAction.toMulAction.toSMul
    letI : SMulCommClass ℤ ℤ C :=
      ⟨fun r s c => (C.hV2.mul_smul r s c).symm.trans
        ((congrArg (fun n : ℤ => C.hV2.smul n c) (Int.mul_comm r s)).trans
          (C.hV2.mul_smul s r c))⟩
    let hf : A ⊗[ℤ] B →ₗ[ℤ] C := f.hom.toLinearMap
    let h : B →ₗ[ℤ] H := (TensorProduct.curry hf).flip
    exact Rep.ofHom ⟨h, fun g => by
      apply LinearMap.ext
      intro x
      change (show A →ₗ[ℤ] C from h (B.ρ g x)) =
        C.ρ g ∘ₗ (show A →ₗ[ℤ] C from h x) ∘ₗ A.ρ g⁻¹
      apply LinearMap.ext
      intro y
      change hf (y ⊗ₜ[ℤ] (B.ρ g x)) = C.ρ g (hf (A.ρ g⁻¹ y ⊗ₜ[ℤ] x))
      have hc : f.hom ((A.ρ.tprod B.ρ) g (A.ρ g⁻¹ y ⊗ₜ[ℤ] x)) =
          C.ρ g (f.hom (A.ρ g⁻¹ y ⊗ₜ[ℤ] x)) :=
        Rep.hom_comm_apply f g (A.ρ g⁻¹ y ⊗ₜ[ℤ] x)
      have ht : (A.ρ.tprod B.ρ) g (A.ρ g⁻¹ y ⊗ₜ[ℤ] x) = y ⊗ₜ[ℤ] B.ρ g x := by
        rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.self_inv_apply]
      exact (congrArg (fun z => f.hom z) ht).symm.trans hc⟩
  invFun f := by
    let H : Rep.{u} ℤ Γ := (Rep.ihom A).obj C
    letI : AddCommGroup H := H.hV1
    letI : Module ℤ H := H.hV2
    letI : Module ℤ C := C.hV2
    letI : MulAction ℤ C := C.hV2.toDistribMulAction.toMulAction
    letI : SMul ℤ C := C.hV2.toDistribMulAction.toMulAction.toSMul
    letI : SMulCommClass ℤ ℤ C :=
      ⟨fun r s c => (C.hV2.mul_smul r s c).symm.trans
        ((congrArg (fun n : ℤ => C.hV2.smul n c) (Int.mul_comm r s)).trans
          (C.hV2.mul_smul s r c))⟩
    let ff : B →ₗ[ℤ] A →ₗ[ℤ] C := f.hom.toLinearMap
    exact Rep.ofHom
      ⟨TensorProduct.uncurry (.id ℤ) _ _ _ ff.flip,
        fun g => TensorProduct.ext' (fun (x : A) (y : B) => by
          change ff (B.ρ g y) (A.ρ g x) = C.ρ g (ff y x)
          have hg : ff (B.ρ g y) = C.ρ g ∘ₗ ff y ∘ₗ A.ρ g⁻¹ :=
            Rep.hom_comm_apply f g y
          simpa using congrArg (fun k : A →ₗ[ℤ] C => k (A.ρ g x)) hg)⟩
  left_inv f := Rep.hom_ext (Representation.IntertwiningMap.ext
    (TensorProduct.ext' (fun x y => rfl)))
  right_inv f := Rep.hom_ext (Representation.IntertwiningMap.ext
    (LinearMap.ext (fun x => LinearMap.ext (fun y => rfl))))

/-- The actual adjunction, including naturality of the same maps. -/
private noncomputable def tensorAdjunction (A : Rep.{u} ℤ Γ) :
    tensorLeft A ⊣ Rep.ihom A := by
  have forwardPoint {B C : Rep.{u} ℤ Γ} (f : (tensorLeft A).obj B ⟶ C) (b : B) (a : A) :
      (show A →ₗ[ℤ] C from ((tensorHomEquiv A B C) f).hom b) a =
        f.hom (a ⊗ₜ[ℤ] b) := by rfl
  have backwardPoint {B C : Rep.{u} ℤ Γ} (f : B ⟶ (Rep.ihom A).obj C) (a : A) (b : B) :
      ((tensorHomEquiv A B C).symm f).hom (a ⊗ₜ[ℤ] b) =
        (show A →ₗ[ℤ] C from f.hom b) a := by rfl
  refine Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv A
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro X' X Y f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro a b
    have hm : ((tensorLeft A).map f).hom (a ⊗ₜ[ℤ] b) = a ⊗ₜ[ℤ] f.hom b := rfl
    calc
      ((tensorHomEquiv A X' Y).symm (f ≫ g)).hom (a ⊗ₜ[ℤ] b) =
          (show A →ₗ[ℤ] Y from g.hom (f.hom b)) a := backwardPoint (f ≫ g) a b
      _ = ((tensorHomEquiv A X Y).symm g).hom (a ⊗ₜ[ℤ] f.hom b) :=
        (backwardPoint g a (f.hom b)).symm
      _ = ((tensorHomEquiv A X Y).symm g).hom
          (((tensorLeft A).map f).hom (a ⊗ₜ[ℤ] b)) :=
        congrArg (fun z => ((tensorHomEquiv A X Y).symm g).hom z) hm.symm
      _ = ((tensorLeft A).map f ≫ (tensorHomEquiv A X Y).symm g).hom (a ⊗ₜ[ℤ] b) := rfl
  · intro X Y Y' f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro b
    change (show A →ₗ[ℤ] Y' from ((tensorHomEquiv A X Y') (f ≫ g)).hom b) =
      (show A →ₗ[ℤ] Y' from (((tensorHomEquiv A X Y) f) ≫ (Rep.ihom A).map g).hom b)
    apply LinearMap.ext
    intro a
    have hm : (show A →ₗ[ℤ] Y' from ((Rep.ihom A).map g).hom
        (((tensorHomEquiv A X Y) f).hom b)) a =
        g.hom ((show A →ₗ[ℤ] Y from ((tensorHomEquiv A X Y) f).hom b) a) := rfl
    exact (forwardPoint (f ≫ g) b a).trans
      ((congrArg (fun z => g.hom z) (forwardPoint f b a).symm).trans hm.symm)

private instance tensorLeft_isLeftAdjoint (A : Rep.{u} ℤ Γ) :
    (tensorLeft A).IsLeftAdjoint := (tensorAdjunction A).isLeftAdjoint

/-- The original coinvariant functor composed with that derived tensor. -/
private noncomputable def stalkFunctor (A : Rep.{u} ℤ Γ) :
    Rep.{u} ℤ Γ ⥤ ModuleCat.{u} ℤ :=
  tensorLeft A ⋙ Rep.coinvariantsFunctor ℤ Γ

private instance stalkFunctor_additive (A : Rep.{u} ℤ Γ) :
    (stalkFunctor A).Additive := by
  change (tensorLeft A ⋙ Rep.coinvariantsFunctor ℤ Γ).Additive
  infer_instance

private instance stalkFunctor_isLeftAdjoint (A : Rep.{u} ℤ Γ) :
    (stalkFunctor A).IsLeftAdjoint := by
  change (tensorLeft A ⋙ Rep.coinvariantsFunctor ℤ Γ).IsLeftAdjoint
  infer_instance

/-- Its value is the same diagonal-action coinvariant tensor, not a new quotient. -/
private theorem stalkFunctor_obj (A B : Rep.{u} ℤ Γ) :
    (stalkFunctor A).obj B = ModuleCat.of ℤ (A.ρ.tprod B.ρ).Coinvariants := by
  let V : ModuleCat.{u} ℤ := (stalkFunctor A).obj B
  let T : Type u := (A.ρ.tprod B.ρ).Coinvariants
  let W : ModuleCat.{u} ℤ := ModuleCat.of ℤ T
  let : AddCommGroup T := V.isAddCommGroup
  let μ : Module ℤ T := V.isModule
  let ν : Module ℤ T := W.isModule
  have h : μ = ν := Subsingleton.elim _ _
  exact congrArg (fun m : Module ℤ T => @ModuleCat.of ℤ _ T _ m) h

/-- Every pure tensor follows the same original representation morphism. -/
private theorem stalkFunctor_map_mk (A : Rep.{u} ℤ Γ) {B C : Rep.{u} ℤ Γ}
    (f : B ⟶ C) (a : A) (b : B) :
    (stalkFunctor A).map f
        (Representation.Coinvariants.mk (A.ρ.tprod B.ρ) (a ⊗ₜ[ℤ] b)) =
      Representation.Coinvariants.mk (A.ρ.tprod C.ρ) (a ⊗ₜ[ℤ] f.hom b) := rfl

/-- The actual functor preserves all coproducts of the original stalk size. -/
private theorem stalkFunctor_preservesCoproducts (A : Rep.{u} ℤ Γ) :
    PreservesColimitsOfSize.{u, u} (stalkFunctor A) := inferInstance

/-- The same actual ring/group representation, expressed as a rank-one free
representation, at arbitrary integer and group universes. -/
private noncomputable def freeOneIsoLeftRegular :
    Rep.free ℤ Γ PUnit.{v + 1} ≅ Rep.leftRegular ℤ Γ := by
  let e : (PUnit.{v + 1} →₀ ℤ[Γ]) ≃ₗ[ℤ] ℤ[Γ] :=
    Finsupp.uniqueLinearEquiv ℤ ℤ[Γ] PUnit.unit
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply LinearMap.ext
  intro a
  have ha : a = Finsupp.single PUnit.unit (a PUnit.unit) := by
    apply Finsupp.ext
    intro i
    have hi : i = PUnit.unit := Subsingleton.elim _ _
    subst i
    exact (Finsupp.single_eq_same).symm
  change e ((Representation.free ℤ Γ PUnit.{v + 1}) g a) =
    Representation.leftRegular ℤ Γ g (e a)
  rw [ha]
  simp only [Representation.free, Representation.finsupp_single, e,
    Finsupp.uniqueLinearEquiv_apply, Finsupp.single_eq_same]

/-- Stock free-module projectivity supplies rank-one projectivity without
matching the integer scalar universe with the original group universe. -/
private theorem leftRegular_projective : Projective (Rep.leftRegular ℤ Γ) :=
  Projective.of_iso freeOneIsoLeftRegular
    (inferInstance : Projective (Rep.free ℤ Γ PUnit.{v + 1}))

/-- The original rank-one coinvariant evaluation on the SAME returned tensor. -/
private noncomputable def regularStalkIso (A : Rep.{v} ℤ Γ) :
    (stalkFunctor A).obj (Rep.leftRegular ℤ Γ) ≅ ModuleCat.of ℤ A := by
  let V : ModuleCat.{v} ℤ := (stalkFunctor A).obj (Rep.leftRegular ℤ Γ)
  letI : AddCommGroup V := V.isAddCommGroup
  letI : Module ℤ V := V.isModule
  letI : Module ℤ A := A.hV2
  let e : V ≃ₗ[ℤ] A := Representation.coinvariantsTprodLeftRegularLEquiv A.ρ
  exact e.toModuleIso

/-- The coefficient formula keeps the noncommutative right-stalk convention. -/
private theorem regularStalkIso_value (A : Rep.{v} ℤ Γ) (a : A) (g : Γ) (n : ℤ) :
    (regularStalkIso A).hom
        (Representation.Coinvariants.mk (A.ρ.tprod (Rep.leftRegular ℤ Γ).ρ)
          (a ⊗ₜ[ℤ] (.single g n : ℤ[Γ]))) = n • A.ρ g⁻¹ a := by
  change Representation.coinvariantsTprodLeftRegularLEquiv A.ρ
      (Representation.Coinvariants.mk _ (a ⊗ₜ[ℤ] (.single g n : ℤ[Γ]))) = _
  rw [Representation.coinvariantsTprodLeftRegularLEquiv_apply,
    Representation.ofCoinvariantsTprodLeftRegular_mk_tmul_single]
  exact int_smul_eq_zsmul A.hV2 n (A.ρ g⁻¹ a)

/-- A bounded projective comparison is transported by the actual additive
stalk functor via its DERIVED homotopy equivalence, without flatness. -/
private theorem stalkFunctor_quasiIso_of_projective
    (A : Rep.{u} ℤ Γ) {K L : ChainComplex (Rep.{u} ℤ Γ) ℕ}
    [∀ n : ℕ, Projective (K.X n)] [∀ n : ℕ, Projective (L.X n)]
    (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso (((stalkFunctor A).mapHomologicalComplex (ComplexShape.down ℕ)).map f) := by
  have he := (ChainComplex.quasiIso_iff_of_projective f).mp hf
  have ht := (stalkFunctor A).homotopyEquivalences_mapHomologicalComplex_map f he
  exact _root_.homotopyEquivalences_le_quasiIso
    (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) _ ht


end ActualIntegerStalkTensor

end

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ActualIntegerStalkTensor
open scoped MonoidAlgebra TensorProduct Simplicial

universe w

namespace ActualOriginalRegularRepresentation

-- Prefer the existing structural module on tensors and linear maps over
-- the competing canonical integer action; all remain the SAME ℤ-modules.
attribute [local instance 1001] TensorProduct.instModule LinearMap.module


local instance (Γ : Type w) [Group Γ] (I : Type w) :
    HasColimitsOfShape (Discrete I) (Rep.{w} ℤ Γ) := inferInstance

local instance (Γ : Type w) [Group Γ] : HasCoproducts.{w} (Rep.{w} ℤ Γ) :=
  fun _I => inferInstance


-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type w) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
  letI : Small.{w} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{w} AddCommGrpCat.{w} :=
  fun I =>
    letI : Small.{w} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type w) : HasColimitsOfShape (Discrete I) (ModuleCat.{w} ℤ) :=
  letI : Small.{w} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{w} (ModuleCat.{w} ℤ) :=
  fun I =>
    letI : Small.{w} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


variable {C : Type w} [Groupoid.{w} C]

/-- The action on the ORIGINAL integral path coefficient module. -/
private noncomputable def pathRepresentation (y x : C) :
    Representation ℤ (Aut y) (FreeAbelianGroup (y ⟶ x)) where
  toFun g := (FreeAbelianGroup.map (fun γ : y ⟶ x => g.asIso.inv ≫ γ)).toIntLinearMap
  map_one' := by
    have hf : (fun γ : y ⟶ x => (1 : Aut y).asIso.inv ≫ γ) = id :=
      funext (fun γ => Category.id_comp γ)
    exact congrArg (fun h : FreeAbelianGroup (y ⟶ x) →+ FreeAbelianGroup (y ⟶ x) =>
      h.toIntLinearMap) ((congrArg FreeAbelianGroup.map hf).trans FreeAbelianGroup.map_id)
  map_mul' g h := by
    have hf : (fun γ : y ⟶ x => (g * h).asIso.inv ≫ γ) =
        (fun γ : y ⟶ x => g.asIso.inv ≫ γ) ∘
          (fun γ : y ⟶ x => h.asIso.inv ≫ γ) := by
      funext γ
      change (g.asIso.inv ≫ h.asIso.inv) ≫ γ =
        g.asIso.inv ≫ (h.asIso.inv ≫ γ)
      exact Category.assoc _ _ _
    exact congrArg (fun k : FreeAbelianGroup (y ⟶ x) →+ FreeAbelianGroup (y ⟶ x) =>
      k.toIntLinearMap) ((congrArg FreeAbelianGroup.map hf).trans FreeAbelianGroup.map_comp)

private theorem pathRepresentation_of (y x : C) (g : Aut y) (γ : y ⟶ x) :
    pathRepresentation y x g (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (g.asIso.inv ≫ γ) := rfl

/-- The same original path coefficient maps, now retaining their action. -/
private noncomputable def pathRepFunctor (y : C) : C ⥤ Rep.{w} ℤ (Aut y) where
  obj x := Rep.of (pathRepresentation y x)
  map {x x'} f := Rep.ofHom
    { __ := ((CategoryTheory.regularPathModuleCoefficientFunctor y).map f).hom
      isIntertwining' g := by
        have h : (CategoryTheory.regularPathCoefficientTransport y f).comp
              (FreeAbelianGroup.map (fun γ : y ⟶ x => g.asIso.inv ≫ γ)) =
            (FreeAbelianGroup.map (fun γ : y ⟶ x' => g.asIso.inv ≫ γ)).comp
              (CategoryTheory.regularPathCoefficientTransport y f) := by
          apply FreeAbelianGroup.lift_ext
          intro γ
          change FreeAbelianGroup.of ((g.asIso.inv ≫ γ) ≫ f) =
            FreeAbelianGroup.of (g.asIso.inv ≫ (γ ≫ f))
          exact congrArg FreeAbelianGroup.of (Category.assoc _ _ _)
        exact congrArg (fun k : FreeAbelianGroup (y ⟶ x) →+ FreeAbelianGroup (y ⟶ x') =>
          k.toIntLinearMap) h }
  map_id x := by
    apply (forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ)).map_injective
    change (CategoryTheory.regularPathModuleCoefficientFunctor y).map (𝟙 x) = 𝟙 _
    exact (CategoryTheory.regularPathModuleCoefficientFunctor y).map_id x
  map_comp f g := by
    apply (forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ)).map_injective
    change (CategoryTheory.regularPathModuleCoefficientFunctor y).map (f ≫ g) =
      (CategoryTheory.regularPathModuleCoefficientFunctor y).map f ≫
        (CategoryTheory.regularPathModuleCoefficientFunctor y).map g
    exact (CategoryTheory.regularPathModuleCoefficientFunctor y).map_comp f g

/-- Forgetting the action preserves the literal ORIGINAL module and transport. -/
private noncomputable def pathRepForgetIso (y : C) :
    pathRepFunctor y ⋙ forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ) ≅
      CategoryTheory.regularPathModuleCoefficientFunctor y :=
  NatIso.ofComponents (fun x => Iso.refl _) (by
    intro x x' f
    change (CategoryTheory.regularPathModuleCoefficientFunctor y).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (CategoryTheory.regularPathModuleCoefficientFunctor y).map f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private theorem pathRepFunctor_map_of (y : C) {x x' : C} (f : x ⟶ x') (γ : y ⟶ x) :
    (pathRepFunctor y).map f (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of (γ ≫ f) :=
  CategoryTheory.regularPathModuleCoefficientFunctor_map_of y f γ

/-- An actual path determines the actual inverse-precomposition torsor chart. -/
private noncomputable def pathTorsorEquiv (y : C) {x : C} (p : y ⟶ x) :
    Aut y ≃ (y ⟶ x) where
  toFun g := g.asIso.inv ≫ p
  invFun γ := Aut.of (asIso p ≪≫ (asIso γ).symm)
  left_inv g := by
    apply Aut.ext
    apply Iso.ext
    change p ≫ inv (g.asIso.inv ≫ p) = g.asIso.hom
    apply (cancel_mono (g.asIso.inv ≫ p)).mp
    calc
      (p ≫ inv (g.asIso.inv ≫ p)) ≫ (g.asIso.inv ≫ p) = p := by
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      _ = g.asIso.hom ≫ (g.asIso.inv ≫ p) := by
        rw [← Category.assoc, g.asIso.hom_inv_id, Category.id_comp]
  right_inv γ := by
    change ((asIso γ).hom ≫ (asIso p).inv) ≫ p = γ
    simp only [Category.assoc, asIso_hom, asIso_inv,
      IsIso.inv_hom_id, Category.comp_id]

private noncomputable def pathChartLinearEquiv (y : C) {x : C} (p : y ⟶ x) :
    ℤ[Aut y] ≃ₗ[ℤ] FreeAbelianGroup (y ⟶ x) := AddEquiv.toIntLinearEquiv
    ((MonoidAlgebra.coeffAddEquiv : ℤ[Aut y] ≃+ (Aut y →₀ ℤ)).trans
      ((FreeAbelianGroup.equivFinsupp (Aut y)).symm.trans
        (FreeAbelianGroup.equivOfEquiv (pathTorsorEquiv y p))))

/-- Every integer and path basis is retained, not just a chosen generator. -/
private theorem pathChartLinearEquiv_single (y : C) {x : C} (p : y ⟶ x)
    (g : Aut y) (n : ℤ) :
    pathChartLinearEquiv y p (.single g n) = n • FreeAbelianGroup.of (g.asIso.inv ≫ p) := by
  change FreeAbelianGroup.map (pathTorsorEquiv y p)
    (Finsupp.toFreeAbelianGroup (MonoidAlgebra.single g n).coeff) = _
  rw [MonoidAlgebra.coeff_single, Finsupp.toFreeAbelianGroup_single,
    map_zsmul, FreeAbelianGroup.map_of_apply]
  rfl

/-- The ORIGINAL path module is genuinely a rank-one projective representation. -/
private noncomputable def pathRegularIso (y : C) {x : C} (p : y ⟶ x) :
    Rep.leftRegular ℤ (Aut y) ≅ (pathRepFunctor y).obj x := by
  let e := pathChartLinearEquiv y p
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply MonoidAlgebra.lhom_ext'
  intro h
  apply LinearMap.ext
  intro n
  change pathChartLinearEquiv y p (Representation.leftRegular ℤ (Aut y) g (.single h n)) =
    pathRepresentation y x g (pathChartLinearEquiv y p (.single h n))
  rw [Representation.ofMulAction_single, pathChartLinearEquiv_single,
    pathChartLinearEquiv_single, map_smul, pathRepresentation_of]
  apply congrArg (fun a => n • a)
  apply congrArg FreeAbelianGroup.of
  change (g.asIso.inv ≫ h.asIso.inv) ≫ p = g.asIso.inv ≫ (h.asIso.inv ≫ p)
  exact Category.assoc _ _ _

private theorem pathRep_object_projective (y : C) {x : C} (p : y ⟶ x) :
    Projective ((pathRepFunctor y).obj x) :=
  Projective.of_iso (pathRegularIso y p) (ActualIntegerStalkTensor.leftRegular_projective)

private theorem pathRegularIso_inv_of (y : C) {x : C} (p γ : y ⟶ x) :
    (pathRegularIso y p).inv.hom (FreeAbelianGroup.of γ) =
      .single ((pathTorsorEquiv y p).symm γ) (1 : ℤ) := by
  let g := (pathTorsorEquiv y p).symm γ
  have hg : g.asIso.inv ≫ p = γ := (pathTorsorEquiv y p).apply_symm_apply γ
  have hf : (pathRegularIso y p).hom.hom (MonoidAlgebra.single g (1 : ℤ)) =
      FreeAbelianGroup.of γ := by
    change pathChartLinearEquiv y p (MonoidAlgebra.single g (1 : ℤ)) = _
    rw [pathChartLinearEquiv_single, hg, one_smul]
  have hi := Rep.inv_hom_apply (Rep.leftRegular ℤ (Aut y))
    ((pathRepFunctor y).obj x) (pathRegularIso y p) (MonoidAlgebra.single g (1 : ℤ))
  exact (congrArg (fun a => (pathRegularIso y p).inv.hom a) hf).symm.trans hi

variable (L : C ⥤ ModuleCat.{w} ℤ)

/-- The target stalk action is computed from the ORIGINAL coefficient functor. -/
private noncomputable def stalkRep (y : C) : Rep.{w} ℤ (Aut y) :=
  Rep.of ((ModuleCat.endRingEquiv (L.obj y)).toMonoidHom.comp
    ((L.mapEnd y).comp (Aut.toEnd (X := y))))

private theorem stalkRep_value (y : C) (g : Aut y) (m : L.obj y) :
    (stalkRep L y).ρ g m = (L.map g.asIso.hom).hom m := rfl

/-- The forward evaluation is computed from the same path chart and stock
regular coinvariant evaluation, followed by the ORIGINAL coefficient map. -/
private noncomputable def pathStalkIso (y : C) {x : C} (p : y ⟶ x) :
    (ActualIntegerStalkTensor.stalkFunctor (stalkRep L y)).obj
      ((pathRepFunctor y).obj x) ≅ L.obj x := by
  exact (ActualIntegerStalkTensor.stalkFunctor (stalkRep L y)).mapIso
      (pathRegularIso y p).symm ≪≫
    ActualIntegerStalkTensor.regularStalkIso (stalkRep L y) ≪≫ L.mapIso (asIso p)

/-- Each ORIGINAL path evaluates through its SAME coefficient transport. -/
private theorem pathStalkIso_mk_of (y : C) {x : C} (p γ : y ⟶ x) (m : L.obj y) :
    (pathStalkIso L y p).hom
        (Representation.Coinvariants.mk
          ((stalkRep L y).ρ.tprod ((pathRepFunctor y).obj x).ρ)
          (m ⊗ₜ[ℤ] FreeAbelianGroup.of γ)) = (L.map γ).hom m := by
  let A : Rep.{w} ℤ (Aut y) := stalkRep L y
  let B : Rep.{w} ℤ (Aut y) := (pathRepFunctor y).obj x
  let F : Rep.{w} ℤ (Aut y) ⥤ ModuleCat.{w} ℤ := ActualIntegerStalkTensor.stalkFunctor A
  let g := (pathTorsorEquiv y p).symm γ
  let b : B := FreeAbelianGroup.of γ
  let qS : F.obj B := Representation.Coinvariants.mk (A.ρ.tprod B.ρ) ((m : A) ⊗ₜ[ℤ] b)
  let qT : F.obj (Rep.leftRegular ℤ (Aut y)) :=
    Representation.Coinvariants.mk (A.ρ.tprod (Rep.leftRegular ℤ (Aut y)).ρ)
      ((m : A) ⊗ₜ[ℤ] MonoidAlgebra.single g (1 : ℤ))
  have hg : g.asIso.inv ≫ p = γ := (pathTorsorEquiv y p).apply_symm_apply γ
  have hb : (pathRegularIso y p).inv.hom b = MonoidAlgebra.single g (1 : ℤ) :=
    pathRegularIso_inv_of y p γ
  have hF : F.map (pathRegularIso y p).inv qS = qT :=
    (ActualIntegerStalkTensor.stalkFunctor_map_mk A (pathRegularIso y p).inv (m : A) b).trans
      (congrArg (fun a : Rep.leftRegular ℤ (Aut y) =>
        Representation.Coinvariants.mk (A.ρ.tprod (Rep.leftRegular ℤ (Aut y)).ρ)
          ((m : A) ⊗ₜ[ℤ] a)) hb)
  have hR : (ActualIntegerStalkTensor.regularStalkIso A).hom qT = A.ρ g⁻¹ (m : A) := by
    simpa only [one_smul] using ActualIntegerStalkTensor.regularStalkIso_value A (m : A) g (1 : ℤ)
  have hA : A.ρ g⁻¹ (m : A) = (L.map g.asIso.inv).hom m :=
    stalkRep_value L y g⁻¹ m
  have hc : (L.map p).hom ((L.map g.asIso.inv).hom m) = (L.map γ).hom m :=
    (congrArg (fun f => f.hom m) (L.map_comp g.asIso.inv p)).symm.trans
      (congrArg (fun k => (L.map k).hom m) hg)
  have ht : (pathStalkIso L y p).hom qS =
      (L.map p).hom ((ActualIntegerStalkTensor.regularStalkIso A).hom
        (F.map (pathRegularIso y p).inv qS)) := rfl
  exact ht.trans
    ((congrArg (fun z => (L.map p).hom ((ActualIntegerStalkTensor.regularStalkIso A).hom z))
      hF).trans
      ((congrArg (fun z => (L.map p).hom z) hR).trans
        ((congrArg (fun z => (L.map p).hom z) hA).trans hc)))

/-- Its inverse is forced by the actual Iso and every-path forward formula. -/
private theorem pathStalkIso_inv (y : C) {x : C} (p γ : y ⟶ x) (m : L.obj x) :
    (pathStalkIso L y p).inv m =
      Representation.Coinvariants.mk _
        ((inv (L.map γ)).hom m ⊗ₜ[ℤ] FreeAbelianGroup.of γ) := by
  let e := pathStalkIso L y p
  let eγ : L.obj y ≅ L.obj x := L.mapIso (asIso γ)
  let : IsIso (L.map γ) := eγ.isIso_hom
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have hf := pathStalkIso_mk_of L y p γ ((inv (L.map γ)).hom m)
  have hγ : (L.map γ).hom ((inv (L.map γ)).hom m) = m :=
    ModuleCat.hom_inv_apply (asIso (L.map γ)) m
  exact (ModuleCat.hom_inv_apply e m).trans (hf.trans hγ).symm

/-- The computed evaluations are natural for arbitrary construction paths;
compatibility is proved, not supplied as a family. -/
private theorem pathStalkIso_naturality (y : C) {x x' : C}
    (p : y ⟶ x) (p' : y ⟶ x') (f : x ⟶ x') :
    (ActualIntegerStalkTensor.stalkFunctor (stalkRep L y)).map ((pathRepFunctor y).map f) ≫
        (pathStalkIso L y p').hom =
      (pathStalkIso L y p).hom ≫ L.map f := by
  let A : Rep.{w} ℤ (Aut y) := stalkRep L y
  let B : Rep.{w} ℤ (Aut y) := (pathRepFunctor y).obj x
  let B' : Rep.{w} ℤ (Aut y) := (pathRepFunctor y).obj x'
  let F : Rep.{w} ℤ (Aut y) ⥤ ModuleCat.{w} ℤ := ActualIntegerStalkTensor.stalkFunctor A
  let q := Representation.Coinvariants.mk (A.ρ.tprod B.ρ)
  let q' := Representation.Coinvariants.mk (A.ρ.tprod B'.ρ)
  let e := pathStalkIso L y p
  let e' := pathStalkIso L y p'
  let mf : F.obj B ⟶ F.obj B' := F.map ((pathRepFunctor y).map f)
  apply ModuleCat.hom_ext
  apply Representation.Coinvariants.hom_ext
  change e'.hom.hom ∘ₗ mf.hom ∘ₗ q = (L.map f).hom ∘ₗ e.hom.hom ∘ₗ q
  apply TensorProduct.ext'
  intro m a
  let hL : FreeAbelianGroup (y ⟶ x) →ₗ[ℤ] L.obj x' :=
    (e'.hom.hom ∘ₗ mf.hom ∘ₗ q) ∘ₗ TensorProduct.mk ℤ A B m
  let hR : FreeAbelianGroup (y ⟶ x) →ₗ[ℤ] L.obj x' :=
    ((L.map f).hom ∘ₗ e.hom.hom ∘ₗ q) ∘ₗ TensorProduct.mk ℤ A B m
  change hL a = hR a
  induction a using FreeAbelianGroup.induction_on with
  | zero => exact (map_zero hL).trans (map_zero hR).symm
  | of γ =>
      let b : B := FreeAbelianGroup.of γ
      let b' : B' := FreeAbelianGroup.of (γ ≫ f)
      have hb : ((pathRepFunctor y).map f).hom b = b' := pathRepFunctor_map_of y f γ
      have hm : mf (q (m ⊗ₜ[ℤ] b)) = q' (m ⊗ₜ[ℤ] b') :=
        (ActualIntegerStalkTensor.stalkFunctor_map_mk A ((pathRepFunctor y).map f) m b).trans
          (congrArg (fun z : B' => q' (m ⊗ₜ[ℤ] z)) hb)
      have he' : e'.hom (q' (m ⊗ₜ[ℤ] b')) = (L.map (γ ≫ f)).hom (m : L.obj y) :=
        pathStalkIso_mk_of L y p' (γ ≫ f) (m : L.obj y)
      have he : e.hom (q (m ⊗ₜ[ℤ] b)) = (L.map γ).hom (m : L.obj y) :=
        pathStalkIso_mk_of L y p γ (m : L.obj y)
      have hc : (L.map (γ ≫ f)).hom (m : L.obj y) =
          (L.map f).hom ((L.map γ).hom (m : L.obj y)) :=
        congrArg (fun k => k.hom (m : L.obj y)) (L.map_comp γ f)
      exact ((congrArg (fun z => e'.hom z) hm).trans he').trans
        (hc.trans (congrArg (fun z => (L.map f).hom z) he).symm)
  | neg a ih =>
      exact (map_neg hL (FreeAbelianGroup.of a)).trans
        ((congrArg Neg.neg ih).trans (map_neg hR (FreeAbelianGroup.of a)).symm)
  | add a b ih₁ ih₂ =>
      exact (map_add hL a b).trans
        ((congrArg₂ HAdd.hAdd ih₁ ih₂).trans (map_add hR a b).symm)

/-- Connectedness selects actual paths; the resulting coefficient Iso has
all compatibility already derived by the preceding all-path theorem. -/
private noncomputable def pathStalkNatIso (y : C) (hconn : ∀ x : C, Nonempty (y ⟶ x)) :
    pathRepFunctor y ⋙ ActualIntegerStalkTensor.stalkFunctor (stalkRep L y) ≅ L :=
  NatIso.ofComponents (fun x => pathStalkIso L y (hconn x).some)
    (fun {x x'} f => pathStalkIso_naturality L y (hconn x).some (hconn x').some f)


open CategoryTheory.CategoryHomology

/-- The existing GENERIC nerve-pullback bar in the actual representation category. -/
private noncomputable def regularRepresentationComplex {T : SSet.{w}}
    (φ : T ⟶ CategoryTheory.nerve C) (y : C) :
    ChainComplex (Rep.{w} ℤ (Aut y)) ℕ :=
  nervePullbackCoefficientComplex φ (pathRepFunctor y)

/-- Its map is the SAME existing original simplex-reindexing chain map. -/
private noncomputable def regularRepresentationBaseMap {T U : SSet.{w}}
    (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve C) (y : C) :
    regularRepresentationComplex (f ≫ ψ) y ⟶ regularRepresentationComplex ψ y :=
  nervePullbackCoefficientBaseComplexMap f ψ (pathRepFunctor y)

/-- Each actual coefficient summand is projective by an actual path,
not by assuming a desired free group-ring basis. -/
private theorem regularRepresentationComplex_projective {T : SSet.{w}}
    (φ : T ⟶ CategoryTheory.nerve C) (y : C)
    (hconn : ∀ x : C, Nonempty (y ⟶ x)) (n : ℕ) :
    Projective ((regularRepresentationComplex φ y).X n) := by
  change Projective (∐ fun σ : T _⦋n⦌ => (pathRepFunctor y).obj
    ((φ.app (Opposite.op ⦋n⦌) σ).left))
  let : ∀ σ : T _⦋n⦌, Projective ((pathRepFunctor y).obj
      ((φ.app (Opposite.op ⦋n⦌) σ).left)) :=
    fun σ => pathRep_object_projective y
      (hconn ((φ.app (Opposite.op ⦋n⦌) σ).left)).some
  infer_instance

/-- Every actual singular simplex keeps its original base-map coefficient leg. -/
private theorem regularRepresentationBaseMap_ι {T U : SSet.{w}}
    (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve C) (y : C)
    (n : ℕ) (σ : T _⦋n⦌) :
    nervePullbackCoefficientι (f ≫ ψ) (pathRepFunctor y) σ ≫
        (regularRepresentationBaseMap f ψ y).f n =
      nervePullbackCoefficientι ψ (pathRepFunctor y)
        (f.app (Opposite.op ⦋n⦌) σ) := by
  have hm : (regularRepresentationBaseMap f ψ y).f n =
      nervePullbackCoefficientBaseMap f ψ (pathRepFunctor y) n :=
    nervePullbackCoefficientBaseComplexMap_f f ψ (pathRepFunctor y) n
  exact (congrArg (fun h =>
    nervePullbackCoefficientι (f ≫ ψ) (pathRepFunctor y) σ ≫ h) hm).trans
      (nervePullbackCoefficientι_baseMap f ψ (pathRepFunctor y) σ)

/-- Once the ACTUAL regular comparison is obtained from ending-fiber acyclicity,
its stalk tensor comparison is derived from projectivity and the actual functor.
This internal theorem does not supply the final original coefficient square. -/
private theorem regularRepresentationBaseMap_stalk_quasiIso {T U : SSet.{w}}
    (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve C) (y : C)
    (hconn : ∀ x : C, Nonempty (y ⟶ x))
    (hreg : QuasiIso (regularRepresentationBaseMap f ψ y)) :
    QuasiIso (((ActualIntegerStalkTensor.stalkFunctor (stalkRep L y)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (regularRepresentationBaseMap f ψ y)) := by
  let : ∀ n : ℕ, Projective ((regularRepresentationComplex (f ≫ ψ) y).X n) :=
    regularRepresentationComplex_projective (f ≫ ψ) y hconn
  let : ∀ n : ℕ, Projective ((regularRepresentationComplex ψ y).X n) :=
    regularRepresentationComplex_projective ψ y hconn
  exact ActualIntegerStalkTensor.stalkFunctor_quasiIso_of_projective
    (stalkRep L y) (regularRepresentationBaseMap f ψ y) hreg


end ActualOriginalRegularRepresentation

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
open scoped Simplicial

universe z

namespace ActualOriginalCoefficientNaturality

-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type z) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{z} :=
  letI : Small.{z} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{z} AddCommGrpCat.{z} :=
  fun I =>
    letI : Small.{z} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type z) : HasColimitsOfShape (Discrete I) (ModuleCat.{z} ℤ) :=
  letI : Small.{z} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{z} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{z} (ModuleCat.{z} ℤ) :=
  fun I =>
    letI : Small.{z} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{z} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


/-- Naturality in the actual target coefficient transformation, including the
original nerve-unit transport on the source summand. -/
private theorem pullbackCoefficientMap_square {X Y : SSet.{z}}
    (f : X ⟶ Y) {L M : SSet.LocalSystem ℤ Y} (α : L ⟶ M) :
    SSet.localCoefficientChainMap
          (CategoryTheory.Functor.whiskerLeft (SSet.mapFundamentalGroupoid f) α) ≫
        SSet.localCoefficientPullbackChainMap f M =
      SSet.localCoefficientPullbackChainMap f L ≫ SSet.localCoefficientChainMap α := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    SSet.localCoefficientChainMap_f, SSet.localCoefficientChainMap_f]
  apply CategoryTheory.CategoryHomology.nervePullbackCoefficient_hom_ext
    (SSet.fundamentalGroupoidNerveUnit X) (L.pullback f)
  intro σ
  let x := ((SSet.fundamentalGroupoidNerveUnit X).app (Opposite.op ⦋n⦌) σ).left
  let y := ((SSet.fundamentalGroupoidNerveUnit Y).app (Opposite.op ⦋n⦌)
    (f.app (Opposite.op ⦋n⦌) σ)).left
  let h : (SSet.mapFundamentalGroupoid f).obj x = y :=
    (SSet.localCoefficientPullbackLeftIndex f σ).symm
  let iL := SSet.localCoefficientι (L.pullback f) σ
  let iM := SSet.localCoefficientι (M.pullback f) σ
  let jL := SSet.localCoefficientι L (f.app (Opposite.op ⦋n⦌) σ)
  let jM := SSet.localCoefficientι M (f.app (Opposite.op ⦋n⦌) σ)
  let a := SSet.localCoefficientMap
    (CategoryTheory.Functor.whiskerLeft (SSet.mapFundamentalGroupoid f) α) n
  let bL := (SSet.localCoefficientPullbackChainMap f L).f n
  let bM := (SSet.localCoefficientPullbackChainMap f M).f n
  let c := SSet.localCoefficientMap α n
  have hia : iL ≫ a = α.app ((SSet.mapFundamentalGroupoid f).obj x) ≫ iM :=
    SSet.localCoefficientι_map
      (CategoryTheory.Functor.whiskerLeft (SSet.mapFundamentalGroupoid f) α) σ
  have hibL : iL ≫ bL = eqToHom (congrArg L.obj h) ≫ jL :=
    SSet.localCoefficientι_pullbackChainMap f L σ
  have hibM : iM ≫ bM = eqToHom (congrArg M.obj h) ≫ jM :=
    SSet.localCoefficientι_pullbackChainMap f M σ
  have hjc : jL ≫ c = α.app y ≫ jM :=
    SSet.localCoefficientι_map α (f.app (Opposite.op ⦋n⦌) σ)
  have heq : α.app ((SSet.mapFundamentalGroupoid f).obj x) ≫ eqToHom (congrArg M.obj h) =
      eqToHom (congrArg L.obj h) ≫ α.app y :=
    CategoryTheory.eqToHom_naturality α.app h
  change iL ≫ (a ≫ bM) = iL ≫ (bL ≫ c)
  have hL : iL ≫ (a ≫ bM) =
      (eqToHom (congrArg L.obj h) ≫ α.app y) ≫ jM :=
    (Category.assoc iL a bM).symm.trans
      ((congrArg (fun k => k ≫ bM) hia).trans
        ((Category.assoc _ iM bM).trans
          ((congrArg (fun k => α.app _ ≫ k) hibM).trans
            ((Category.assoc _ _ jM).symm.trans
              (congrArg (fun k => k ≫ jM) heq)))))
  have hR : iL ≫ (bL ≫ c) =
      (eqToHom (congrArg L.obj h) ≫ α.app y) ≫ jM :=
    (Category.assoc iL bL c).symm.trans
      ((congrArg (fun k => k ≫ c) hibL).trans
        ((Category.assoc _ jL c).trans
          ((congrArg (fun k => eqToHom (congrArg L.obj h) ≫ k) hjc).trans
            (Category.assoc _ _ jM).symm)))
  exact hL.trans hR.symm

end ActualOriginalCoefficientNaturality

end

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology HomologicalComplex
open ActualOriginalRegularRepresentation
open scoped Simplicial

universe w

namespace ActualOriginalMapCalibration

-- Prefer the existing structural module on tensors and linear maps over
-- the competing canonical integer action; all remain the SAME ℤ-modules.
attribute [local instance 1001] TensorProduct.instModule LinearMap.module


local instance (Γ : Type w) [Group Γ] (I : Type w) :
    HasColimitsOfShape (Discrete I) (Rep.{w} ℤ Γ) := inferInstance

local instance (Γ : Type w) [Group Γ] : HasCoproducts.{w} (Rep.{w} ℤ Γ) :=
  fun _I => inferInstance


-- These are the existing canonical colimit choices, installed locally to
-- avoid re-solving a forall-index coproduct problem at every occurrence.
local instance (I : Type w) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
  letI : Small.{w} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance : HasCoproducts.{w} AddCommGrpCat.{w} :=
  fun I =>
    letI : Small.{w} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type w) : HasColimitsOfShape (Discrete I) (ModuleCat.{w} ℤ) :=
  letI : Small.{w} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{w} (ModuleCat.{w} ℤ) :=
  fun I =>
    letI : Small.{w} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)


/-- This equality follows from the previously constructed identity-component
forgetful Iso. It is an equality of actual functors, not a replacement model. -/
private theorem pathRepForget_eq {C : Type w} [Groupoid.{w} C] (y : C) :
    pathRepFunctor y ⋙ forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ) =
      CategoryTheory.regularPathModuleCoefficientFunctor y :=
  CategoryTheory.Functor.ext_of_iso (pathRepForgetIso y)
    (fun _ => rfl) (fun _ => rfl)

/-- Coefficient equality transports the SAME existing base map. -/
private theorem baseMap_coefficient_eq {G : Type w} [Category.{w} G]
    {T U : SSet.{w}} (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve G)
    {M N : G ⥤ ModuleCat.{w} ℤ} (h : M = N) :
    nervePullbackCoefficientBaseComplexMap f ψ M ≫
        (eqToIso (congrArg (fun P => nervePullbackCoefficientComplex ψ P) h)).hom =
      (eqToIso (congrArg (fun P => nervePullbackCoefficientComplex (f ≫ ψ) P) h)).hom ≫
        nervePullbackCoefficientBaseComplexMap f ψ N := by
  subst N
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Forgetting the representation action gives the literal original integral
path coefficient complex by the preserved-coproduct comparison. -/
private noncomputable def forgetRegularComplexIso {C : Type w} [Groupoid.{w} C]
    {T : SSet.{w}} (φ : T ⟶ CategoryTheory.nerve C) (y : C) :
    (((forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (regularRepresentationComplex φ y)) ≅
        nervePullbackCoefficientComplex φ
          (CategoryTheory.regularPathModuleCoefficientFunctor y) :=
  nervePullbackCoefficientComplexChangeOfCategoryIso (forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ))
    φ (pathRepFunctor y) ≪≫
    eqToIso (congrArg (fun P => nervePullbackCoefficientComplex φ P) (pathRepForget_eq y))

/-- BOTH actual original base maps commute with the computed forgetful Iso. -/
private theorem forgetRegularComplexIso_base {C : Type w} [Groupoid.{w} C]
    {T U : SSet.{w}} (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve C) (y : C) :
    ((forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (regularRepresentationBaseMap f ψ y) ≫
        (forgetRegularComplexIso ψ y).hom =
      (forgetRegularComplexIso (f ≫ ψ) y).hom ≫
        nervePullbackCoefficientBaseComplexMap f ψ
          (CategoryTheory.regularPathModuleCoefficientFunctor y) := by
  let U := forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ)
  let m := regularRepresentationBaseMap f ψ y
  let b := nervePullbackCoefficientBaseComplexMap f ψ (pathRepFunctor y ⋙ U)
  let c := nervePullbackCoefficientBaseComplexMap f ψ
    (CategoryTheory.regularPathModuleCoefficientFunctor y)
  let eS := nervePullbackCoefficientComplexChangeOfCategoryIso U (f ≫ ψ) (pathRepFunctor y)
  let eT := nervePullbackCoefficientComplexChangeOfCategoryIso U ψ (pathRepFunctor y)
  let zS := eqToIso (congrArg (fun P => nervePullbackCoefficientComplex (f ≫ ψ) P)
    (pathRepForget_eq y))
  let zT := eqToIso (congrArg (fun P => nervePullbackCoefficientComplex ψ P)
    (pathRepForget_eq y))
  have s₁ : CommSq ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map m)
      eS.hom eT.hom b :=
    ⟨nervePullbackCoefficientComplexChangeOfCategoryIso_base U (pathRepFunctor y) f ψ⟩
  have s₂ : CommSq b zS.hom zT.hom c :=
    ⟨baseMap_coefficient_eq f ψ (pathRepForget_eq y)⟩
  exact (CommSq.vert_comp s₁ s₂).w

/-- The same actual regular module map is reflected to a quasi-isomorphism
in representations by the stock exact forgetful functor. -/
private theorem regularRepresentationBaseMap_quasiIso_of_original
    {C : Type w} [Groupoid.{w} C] {T U : SSet.{w}}
    (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve C) (y : C)
    (h : QuasiIso (nervePullbackCoefficientBaseComplexMap f ψ
      (CategoryTheory.regularPathModuleCoefficientFunctor y))) :
    QuasiIso (regularRepresentationBaseMap f ψ y) := by
  let V := forget₂ (Rep.{w} ℤ (Aut y)) (ModuleCat.{w} ℤ)
  let m := regularRepresentationBaseMap f ψ y
  let b := nervePullbackCoefficientBaseComplexMap f ψ
    (CategoryTheory.regularPathModuleCoefficientFunctor y)
  let eS := forgetRegularComplexIso (f ≫ ψ) y
  let eT := forgetRegularComplexIso ψ y
  let e : Arrow.mk ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map m) ≅ Arrow.mk b :=
    Arrow.isoMk eS eT (forgetRegularComplexIso_base f ψ y).symm
  have hm : QuasiIso ((V.mapHomologicalComplex (ComplexShape.down ℕ)).map m) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e).mpr h
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology m V).mp hm

/-- The computed stalk tensor comparison preserves the SAME raw base map.
The projectivity and tensor-Hom adjunction used here are derived above. -/
private theorem stalkBaseMap_quasiIso_of_original
    {C : Type w} [Groupoid.{w} C] {T U : SSet.{w}}
    (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve C)
    (L : C ⥤ ModuleCat.{w} ℤ) (y : C)
    (hconn : ∀ x : C, Nonempty (y ⟶ x))
    (h : QuasiIso (nervePullbackCoefficientBaseComplexMap f ψ
      (CategoryTheory.regularPathModuleCoefficientFunctor y))) :
    QuasiIso (nervePullbackCoefficientBaseComplexMap f ψ
      (pathRepFunctor y ⋙ ActualIntegerStalkTensor.stalkFunctor (stalkRep L y))) := by
  let A := stalkRep L y
  let F := ActualIntegerStalkTensor.stalkFunctor A
  let m := regularRepresentationBaseMap f ψ y
  let N := pathRepFunctor y ⋙ F
  have hm : QuasiIso m := regularRepresentationBaseMap_quasiIso_of_original f ψ y h
  have ht : QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map m) :=
    regularRepresentationBaseMap_stalk_quasiIso L f ψ y hconn hm
  let e : Arrow.mk ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map m) ≅
      Arrow.mk (nervePullbackCoefficientBaseComplexMap f ψ N) :=
    Arrow.isoMk (nervePullbackCoefficientComplexChangeOfCategoryIso F (f ≫ ψ) (pathRepFunctor y))
      (nervePullbackCoefficientComplexChangeOfCategoryIso F ψ (pathRepFunctor y))
      (nervePullbackCoefficientComplexChangeOfCategoryIso_base F (pathRepFunctor y) f ψ).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e).mp ht

/-- The source transport is forced by the actual nerve-unit naturality
identity. It is not an assumed edge calibration. -/
private noncomputable def originalPullbackSourceIso {X Y : SSet.{w}}
    (f : X ⟶ Y) (L : SSet.LocalSystem ℤ Y) :
    SSet.localCoefficientChainComplex (L.pullback f) ≅
      nervePullbackCoefficientComplex (f ≫ SSet.fundamentalGroupoidNerveUnit Y) L := by
  let φ : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    SSet.fundamentalGroupoidNerveUnit X ≫ CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)
  let ψ : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    f ≫ SSet.fundamentalGroupoidNerveUnit Y
  have h : φ = ψ := (SSet.fundamentalGroupoidNerveUnit_naturality f).symm
  let e : nervePullbackCoefficientComplex φ L ≅ nervePullbackCoefficientComplex ψ L :=
    eqToIso (congrArg (fun q : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) =>
      nervePullbackCoefficientComplex q L) h)
  exact e

/-- The SAME original pullback chain map is exactly the source transport
followed by the existing arbitrary-source bar base map, in every degree. -/
private theorem originalPullbackChainMap_eq_source_base {X Y : SSet.{w}}
    (f : X ⟶ Y) (L : SSet.LocalSystem ℤ Y) :
    SSet.localCoefficientPullbackChainMap f L =
      (originalPullbackSourceIso f L).hom ≫
        nervePullbackCoefficientBaseComplexMap f (SSet.fundamentalGroupoidNerveUnit Y) L := by
  ext n : 1
  let φ : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    SSet.fundamentalGroupoidNerveUnit X ≫ CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f)
  let ψ : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) :=
    f ≫ SSet.fundamentalGroupoidNerveUnit Y
  have hφ : φ = ψ := (SSet.fundamentalGroupoidNerveUnit_naturality f).symm
  let H : nervePullbackCoefficientComplex φ L = nervePullbackCoefficientComplex ψ L :=
    congrArg (fun q : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid Y) =>
      nervePullbackCoefficientComplex q L) hφ
  have he : (originalPullbackSourceIso f L).hom.f n =
      eqToHom (SSet.localCoefficientPullbackObjEq f L n) :=
    HomologicalComplex.eqToHom_f H n
  have hb : (nervePullbackCoefficientBaseComplexMap f
      (SSet.fundamentalGroupoidNerveUnit Y) L).f n =
      nervePullbackCoefficientBaseMap f (SSet.fundamentalGroupoidNerveUnit Y) L n :=
    nervePullbackCoefficientBaseComplexMap_f f (SSet.fundamentalGroupoidNerveUnit Y) L n
  have hc : ((originalPullbackSourceIso f L).hom ≫
      nervePullbackCoefficientBaseComplexMap f (SSet.fundamentalGroupoidNerveUnit Y) L).f n =
      eqToHom (SSet.localCoefficientPullbackObjEq f L n) ≫
        nervePullbackCoefficientBaseMap f (SSet.fundamentalGroupoidNerveUnit Y) L n :=
    (HomologicalComplex.comp_f _ _ n).trans (congrArg₂ (fun a b => a ≫ b) he hb)
  exact (SSet.localCoefficientPullbackChainMap_f f L n).trans hc.symm

/-- The actual local-coefficient source transport does not change whether
its original base map is a quasi-isomorphism. -/
private theorem originalPullbackChainMap_quasiIso_iff_raw {X Y : SSet.{w}}
    (f : X ⟶ Y) (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) ↔
      QuasiIso (nervePullbackCoefficientBaseComplexMap f
        (SSet.fundamentalGroupoidNerveUnit Y) L) := by
  rw [originalPullbackChainMap_eq_source_base]
  exact quasiIso_iff_comp_left
    (originalPullbackSourceIso f L).hom
    (nervePullbackCoefficientBaseComplexMap f (SSet.fundamentalGroupoidNerveUnit Y) L)

/-- A computed coefficient Iso transfers quasi-isomorphy through the WHOLE
actual original pullback-map square. -/
private theorem originalPullback_quasiIso_of_coefficientIso {X Y : SSet.{w}}
    (f : X ⟶ Y) {L M : SSet.LocalSystem ℤ Y} (e : L ≅ M)
    (h : QuasiIso (SSet.localCoefficientPullbackChainMap f L)) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f M) := by
  let eS := (SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := X)).mapIso
    (CategoryTheory.Functor.isoWhiskerLeft (SSet.mapFundamentalGroupoid f) e)
  let eT := (SSet.localCoefficientChainComplexFunctor (R := ℤ) (X := Y)).mapIso e
  have hs : SSet.localCoefficientPullbackChainMap f L ≫ eT.hom =
      eS.hom ≫ SSet.localCoefficientPullbackChainMap f M :=
    (ActualOriginalCoefficientNaturality.pullbackCoefficientMap_square f e.hom).symm
  let a : Arrow.mk (SSet.localCoefficientPullbackChainMap f L) ≅
      Arrow.mk (SSet.localCoefficientPullbackChainMap f M) := Arrow.isoMk eS eT hs.symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _ a).mp h

/-- EVERY target stalk follows its actual coefficient transports. No flatness,
homology-preserving tensor, supplied representation comparison or model is input. -/
public theorem originalAllCoefficientPullback_quasiIso_of_regular
    {X Y : SSet.{w}} (f : X ⟶ Y) (y : Y _⦋0⦌)
    (hconn : ∀ x : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ x))
    (hreg : QuasiIso (SSet.localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))))
    (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) := by
  let C := SSet.FundamentalGroupoid Y
  let b : C := SSet.FundamentalGroupoid.mk y
  let F := ActualIntegerStalkTensor.stalkFunctor (stalkRep L b)
  let N : SSet.LocalSystem ℤ Y := pathRepFunctor b ⋙ F
  have hr : QuasiIso (nervePullbackCoefficientBaseComplexMap f
      (SSet.fundamentalGroupoidNerveUnit Y)
      (CategoryTheory.regularPathModuleCoefficientFunctor b)) :=
    (originalPullbackChainMap_quasiIso_iff_raw f _).mp hreg
  have hN : QuasiIso (nervePullbackCoefficientBaseComplexMap f
      (SSet.fundamentalGroupoidNerveUnit Y) N) :=
    stalkBaseMap_quasiIso_of_original f (SSet.fundamentalGroupoidNerveUnit Y) L b hconn hr
  have hN' : QuasiIso (SSet.localCoefficientPullbackChainMap f N) :=
    (originalPullbackChainMap_quasiIso_iff_raw f N).mpr hN
  exact originalPullback_quasiIso_of_coefficientIso f (pathStalkNatIso L b hconn) hN'

end ActualOriginalMapCalibration

end
