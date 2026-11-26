/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels

/-!
# Ordinary constant-coefficient module quasi-equivalence

Given two inputs, the normalization witness `C : ConstantRingSource A N` for the
shuffle normalization of a constant ring and the comparison functor's compatibility
data `J : OrdinaryModuleSource A N C`, the native comparison `J.functor` from
ordinary module complexes to DG modules is a DG quasi-equivalence. Both inputs are
hypotheses of the theorem; their constructions remain wanted.

Source for the degree-zero DG comparison: Bernhard Keller, *Deriving DG categories*,
Section 2.1.
Motivation only, since it concerns arc-hyperdescent rather than this comparison:
Bhargav Bhatt and Akhil Mathew, *The arc-topology*, Section 5.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open OrdinarySchemeModuleFamilies
open MathlibExt.DGSource
open CochainComplex.HomComplex
attribute [local instance 2000] ModuleCat.instLinear

private theorem scalar_naturality (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (F G : ModuleComplexes A) (n p q : ℤ) (h : p + n = q)
    (η : letI := moduleDG A; letI := (ringCategory A N).dg;
      DGHom ℤ n (J.functor.obj F) (J.functor.obj G))
    (r : A) (m : (ringValue A N (J.functor.obj F)).X p) :
    letI := (ringCategory A N).dg
    ((DGFunctor.dgApp (C := (ringCategory A N)ᵒᵖ) ℤ n
      (Opposite.op (PUnit.unit : ringCategory A N)) η : Cochain _ _ n).v p q h).hom
        (((J.functor.obj F).toEnrichedFunctor.dgMap 0 (scalar A N C r) :
          Cochain _ _ 0).v p p (add_zero p) m) =
      ((J.functor.obj G).toEnrichedFunctor.dgMap 0 (scalar A N C r) :
        Cochain _ _ 0).v q q (add_zero q)
        (((DGFunctor.dgApp (C := (ringCategory A N)ᵒᵖ) ℤ n
          (Opposite.op (PUnit.unit : ringCategory A N)) η : Cochain _ _ n).v p q h).hom m) := by
  dsimp only
  let _ := moduleDG A
  let _ := (ringCategory A N).dg
  have hn := DGFunctor.dgComp_dgMap_dgApp (C := (ringCategory A N)ᵒᵖ) ℤ η (scalar A N C r)
    (zero_add n) (add_zero n)
  have hv := congrArg (fun z : DGHom ℤ n
    (ringValue A N (J.functor.obj F)) (ringValue A N (J.functor.obj G)) =>
      ((z : Cochain _ _ n).v p q h).hom m) hn
  simpa only [dgComp_v ℤ _ _ _ p p q (add_zero p) h,
    dgComp_v ℤ _ _ _ p q q h (add_zero q), zero_mul, mul_zero,
    Int.negOnePow_zero, one_smul, ModuleCat.hom_comp, LinearMap.comp_apply] using hv

private theorem inverse_action (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (F : ModuleComplexes A) (r : A) (i : ℤ) (m : F.X i) :
    letI := (ringCategory A N).dg
    ((J.object F).inv.f i).hom (r • m) =
      (((J.functor.obj F).toEnrichedFunctor.dgMap 0 (scalar A N C r) :
        Cochain _ _ 0).v i i (add_zero i)).hom (((J.object F).inv.f i).hom m) := by
  let _ := (ringCategory A N).dg
  let e := (HomologicalComplex.eval (ModuleCat ℤ) (.up ℤ) i).mapIso (J.object F)
  have ha : e.hom.hom
      ((((J.functor.obj F).toEnrichedFunctor.dgMap 0 (scalar A N C r) :
        Cochain _ _ 0).v i i (add_zero i)).hom (e.inv.hom m)) =
      r • (show F.X i from e.hom.hom (e.inv.hom m)) := J.action F r i (e.inv.hom m)
  have hround : e.hom.hom (e.inv.hom m) = m := by
    change (e.inv ≫ e.hom).hom m = m
    rw [e.inv_hom_id]
    rfl
  rw [hround] at ha
  have hback (v : (ringValue A N (J.functor.obj F)).X i) :
      e.inv.hom (e.hom.hom v) = v := by
    change (e.hom ≫ e.inv).hom v = v
    rw [e.hom_inv_id]
    rfl
  have hi := congrArg e.inv.hom ha
  rw [hback] at hi
  simpa only [e, Functor.mapIso,
    HomologicalComplex.eval_map, HomologicalComplex.eval_obj] using hi.symm

private noncomputable def pullComponent (A : OrdinaryAlgebras)
    (N : ShuffleAlgebraFunctor ℤ) (C : ConstantRingSource A N)
    (J : OrdinaryModuleSource A N C) (F G : ModuleComplexes A)
    (n p q : ℤ) (h : p + n = q)
    (η : letI := moduleDG A; letI := (ringCategory A N).dg;
      DGHom ℤ n (J.functor.obj F) (J.functor.obj G)) : F.X p ⟶ G.X q := by
  let _ := moduleDG A
  let _ := (ringCategory A N).dg
  let v := ((DGFunctor.dgApp (C := (ringCategory A N)ᵒᵖ)
    ℤ n (Opposite.op (PUnit.unit : ringCategory A N)) η : Cochain _ _ n).v p q h).hom
  exact ModuleCat.ofHom
    { toFun := fun m => ((J.object G).hom.f q).hom (v (((J.object F).inv.f p).hom m))
      map_add' := by
        intro m m'
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro r m
        change ((J.object G).hom.f q).hom
          (v (((J.object F).inv.f p).hom (r • m))) =
          r • (show G.X q from
            ((J.object G).hom.f q).hom (v (((J.object F).inv.f p).hom m)))
        rw [inverse_action A N C J F r p m,
          scalar_naturality A N C J F G n p q h η r (((J.object F).inv.f p).hom m)]
        exact J.action G r q _ }

private theorem map_injective (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (F G : ModuleComplexes A) (n : ℤ) :
    letI := moduleDG A
    Function.Injective (J.functor.dgMap (X := F) (Y := G) n) := by
  let _ := moduleDG A
  intro f g h
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [← J.homogeneous F G n p q hpq f m,
    ← J.homogeneous F G n p q hpq g m, h]

private theorem map_surjective (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (F G : ModuleComplexes A) (n : ℤ) :
    letI := moduleDG A
    Function.Surjective (J.functor.dgMap (X := F) (Y := G) n) := by
  let _ := moduleDG A
  let _ := (ringCategory A N).dg
  intro η
  let f : DGHom ℤ n F G := Cochain.mk fun p q h => pullComponent A N C J F G n p q h η
  refine ⟨f, ?_⟩
  apply DGFunctor.dgHom_ext
  intro x
  let _ : Subsingleton (ringCategory A N) := by
    change Subsingleton PUnit
    infer_instance
  have hx : x = Opposite.op (PUnit.unit : ringCategory A N) := Subsingleton.elim _ _
  subst x
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply (ConcreteCategory.bijective_of_isIso ((J.object G).hom.f q)).1
  let e := (HomologicalComplex.eval (ModuleCat ℤ) (.up ℤ) p).mapIso (J.object F)
  have hr : e.inv.hom (e.hom.hom m) = m := by
    change (e.hom ≫ e.inv).hom m = m
    rw [e.hom_inv_id]
    rfl
  have hr' : ((J.object F).inv.f p).hom (((J.object F).hom.f p).hom m) = m := by
    simpa only [e, Functor.mapIso, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj] using hr
  have hh := J.homogeneous F G n p q hpq f (((J.object F).hom.f p).hom m)
  change ((J.object G).hom.f q).hom
      (((DGFunctor.dgApp (C := (ringCategory A N)ᵒᵖ) ℤ n
        (Opposite.op (PUnit.unit : ringCategory A N)) (J.functor.dgMap n f) :
          Cochain _ _ n).v p q hpq).hom
        (((J.object F).inv.f p).hom (((J.object F).hom.f p).hom m))) =
    ((J.object G).hom.f q).hom
      (((DGFunctor.dgApp (C := (ringCategory A N)ᵒᵖ) ℤ n
        (Opposite.op (PUnit.unit : ringCategory A N)) η : Cochain _ _ n).v p q hpq).hom
        (((J.object F).inv.f p).hom (((J.object F).hom.f p).hom m))) at hh
  simpa only [hr'] using hh

private theorem hom_map_isIso (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (F G : ModuleComplexes A) :
    letI := moduleDG A
    IsIso (J.functor.map F G) := by
  let _ := moduleDG A
  have h (n : ℤ) : IsIso ((J.functor.map F G).f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro f g hfg
      apply map_injective A N C J F G n
      simpa only [EnrichedFunctor.dgMap_apply] using hfg
    · intro η
      obtain ⟨f, hf⟩ := map_surjective A N C J F G n η
      exact ⟨f, by simpa only [EnrichedFunctor.dgMap_apply] using hf⟩
  let _ := h
  exact HomologicalComplex.Hom.isIso_of_components _

private noncomputable abbrev regularComplex (A : OrdinaryAlgebras) : ModuleComplexes A :=
  discreteModule A (ModuleCat.of A A)

private theorem coefficient_detect (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (a : letI := (ringCategory A N).dg;
      DGHom (C := (ringCategory A N)ᵒᵖ) ℤ 0
        (Opposite.op PUnit.unit) (Opposite.op PUnit.unit)) :
    letI := (ringCategory A N).dg
    ((J.object (regularComplex A)).hom.f 0).hom
      ((((J.functor.obj (regularComplex A)).toEnrichedFunctor.dgMap 0 a :
        Cochain _ _ 0).v 0 0 (add_zero 0)).hom
        (((J.object (regularComplex A)).inv.f 0).hom (1 : A))) =
      C.degree_zero.hom.hom a := by
  let _ := (ringCategory A N).dg
  have ha : scalar A N C (C.degree_zero.hom.hom a) = a := by
    change C.degree_zero.inv.hom (C.degree_zero.hom.hom a) = a
    change (C.degree_zero.hom ≫ C.degree_zero.inv).hom a = a
    rw [C.degree_zero.hom_inv_id]
    rfl
  have hh := J.action (regularComplex A) (C.degree_zero.hom.hom a) 0
    (((J.object (regularComplex A)).inv.f 0).hom (1 : A))
  have hr : ((J.object (regularComplex A)).hom.f 0).hom
      (((J.object (regularComplex A)).inv.f 0).hom (1 : A)) = (1 : A) := by
    change (((J.object (regularComplex A)).inv ≫ (J.object (regularComplex A)).hom).f 0).hom
      (1 : A) = (1 : A)
    rw [Iso.inv_hom_id]
    rfl
  simpa only [ha, hr, smul_eq_mul, mul_one] using hh

private theorem scalar_one (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C) :
    letI := (ringCategory A N).dg
    scalar A N C 1 = dgId (C := (ringCategory A N)ᵒᵖ) ℤ (Opposite.op PUnit.unit) := by
  let _ := (ringCategory A N).dg
  apply (ConcreteCategory.bijective_of_isIso C.degree_zero.hom).1
  have h := coefficient_detect A N C J
    (dgId (C := (ringCategory A N)ᵒᵖ) ℤ (Opposite.op PUnit.unit))
  rw [EnrichedFunctor.dgMap_dgId, dgId_linearHomComplex, Cochain.ofHom_v,
    HomologicalComplex.id_f, ModuleCat.id_apply] at h
  have hr : ((J.object (regularComplex A)).hom.f 0).hom
      (((J.object (regularComplex A)).inv.f 0).hom (1 : A)) = (1 : A) := by
    change (((J.object (regularComplex A)).inv ≫ (J.object (regularComplex A)).hom).f 0).hom
      (1 : A) = (1 : A)
    rw [Iso.inv_hom_id]
    rfl
  rw [hr] at h
  change C.degree_zero.hom.hom (C.degree_zero.inv.hom (1 : A)) = _
  change (C.degree_zero.inv ≫ C.degree_zero.hom).hom (1 : A) = _
  rw [C.degree_zero.inv_hom_id]
  exact h

private theorem scalar_mul (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C) (r s : A) :
    letI := (ringCategory A N).dg
    scalar A N C (r * s) = dgComp ℤ (scalar A N C r) (scalar A N C s) (zero_add 0) := by
  let _ := (ringCategory A N).dg
  apply (ConcreteCategory.bijective_of_isIso C.degree_zero.hom).1
  have h := coefficient_detect A N C J
    (dgComp ℤ (scalar A N C r) (scalar A N C s) (zero_add 0))
  simp only [EnrichedFunctor.dgMap_dgComp, dgComp_linearHomComplex, zero_mul,
    Int.negOnePow_zero, one_smul, Cochain.comp_zero_cochain_v,
    ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [J.action, J.action] at h
  have hr : ((J.object (regularComplex A)).hom.f 0).hom
      (((J.object (regularComplex A)).inv.f 0).hom (1 : A)) = (1 : A) := by
    change (((J.object (regularComplex A)).inv ≫ (J.object (regularComplex A)).hom).f 0).hom
      (1 : A) = (1 : A)
    rw [Iso.inv_hom_id]
    rfl
  rw [hr] at h
  change C.degree_zero.hom.hom (C.degree_zero.inv.hom (r * s)) = _
  change (C.degree_zero.inv ≫ C.degree_zero.hom).hom (r * s) = _
  rw [C.degree_zero.inv_hom_id]
  change s * (r * (1 : A)) = C.degree_zero.hom.hom
    (dgComp ℤ (scalar A N C r) (scalar A N C s) (zero_add 0)) at h
  change r * s = C.degree_zero.hom.hom
    (dgComp ℤ (scalar A N C r) (scalar A N C s) (zero_add 0))
  simpa only [mul_one, mul_comm] using h

@[instance_reducible]
private noncomputable def nativeModule (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (P : MathlibExt.CategoryTheory.DGQuasiFunctorModels.RightModule ℤ (ringCategory A N))
    (i : ℤ) : Module A ((ringValue A N P).X i) := by
  let _ := (ringCategory A N).dg
  let act (r : A) (m : (ringValue A N P).X i) :=
    (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) : Cochain _ _ 0).v i i (add_zero i)).hom m)
  exact
    { smul := act
      one_smul := by
        intro m
        change (((P.toEnrichedFunctor.dgMap 0 (scalar A N C 1) :
          Cochain _ _ 0).v i i (add_zero i)).hom m) = m
        rw [scalar_one A N C J, EnrichedFunctor.dgMap_dgId, dgId_linearHomComplex,
          Cochain.ofHom_v, HomologicalComplex.id_f]
        rfl
      mul_smul := by
        intro r s m
        change (((P.toEnrichedFunctor.dgMap 0 (scalar A N C (r * s)) :
          Cochain _ _ 0).v i i (add_zero i)).hom m) = act r (act s m)
        rw [mul_comm r s, scalar_mul A N C J s r, EnrichedFunctor.dgMap_dgComp,
          dgComp_linearHomComplex, zero_mul, Int.negOnePow_zero, one_smul,
          Cochain.comp_zero_cochain_v]
        rfl
      smul_zero := by intro r; exact map_zero _
      smul_add := by intro r m m'; exact map_add _ m m'
      add_smul := by
        intro r s m
        change act (r + s) m = act r m + act s m
        simp only [act, scalar, map_add]
        change (((P.toEnrichedFunctor.dgMap 0 (C.degree_zero.inv.hom r) : Cochain _ _ 0) +
          (P.toEnrichedFunctor.dgMap 0 (C.degree_zero.inv.hom s) : Cochain _ _ 0)).v
            i i (add_zero i)).hom m = _
        rw [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
      zero_smul := by
        intro m
        change act 0 m = 0
        simp only [act, scalar, map_zero, Cochain.zero_v, ModuleCat.hom_zero,
          LinearMap.zero_apply] }

private theorem scalar_closed (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (r : A) :
    letI := (ringCategory A N).dg
    dgDifferential ℤ 0 (scalar A N C r) = 0 := by
  let _ := (ringCategory A N).dg
  exact @Subsingleton.elim _
    (ModuleCat.isZero_iff_subsingleton.1 (C.off_zero 1 (by decide))) _ _

private noncomputable def scalarChainMap (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N)
    (P : MathlibExt.CategoryTheory.DGQuasiFunctorModels.RightModule ℤ (ringCategory A N))
    (r : A) : ringValue A N P ⟶ ringValue A N P := by
  let _ := (ringCategory A N).dg
  apply Cocycle.homOf
  apply Cocycle.mk (P.toEnrichedFunctor.dgMap 0 (scalar A N C r)) 1 (by omega)
  have h := P.toEnrichedFunctor.dgMap_dgDifferential (scalar A N C r)
  rw [scalar_closed A N C r, map_zero] at h
  simpa only [dgDifferential_linearHomComplex, zero_add] using! h.symm

private noncomputable def nativeComplex (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C)
    (P : MathlibExt.CategoryTheory.DGQuasiFunctorModels.RightModule ℤ (ringCategory A N)) :
    ModuleComplexes A where
  X i := letI := nativeModule A N C J P i; ModuleCat.of A ((ringValue A N P).X i)
  d i j := by
    let _ := nativeModule A N C J P i
    let _ := nativeModule A N C J P j
    exact ModuleCat.ofHom
      { toFun := ((ringValue A N P).d i j).hom
        map_add' := map_add _
        map_smul' := by
          intro r m
          let _ := (ringCategory A N).dg
          change ((ringValue A N P).d i j).hom
            (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
              Cochain _ _ 0).v i i (add_zero i)).hom m) =
            (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
              Cochain _ _ 0).v j j (add_zero j)).hom (((ringValue A N P).d i j).hom m))
          have h := (scalarChainMap A N C P r).comm i j
          simpa only [scalarChainMap, Cocycle.homOf_f, Cocycle.mk_coe,
            ModuleCat.hom_comp, LinearMap.comp_apply] using congrArg (fun f => f.hom m) h }
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ((ringValue A N P).d i j).hom m = 0
    rw [(ringValue A N P).shape i j h]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ((ringValue A N P).d j k).hom (((ringValue A N P).d i j).hom m) = 0
    change ((ringValue A N P).d i j ≫ (ringValue A N P).d j k).hom m = 0
    rw [HomologicalComplex.d_comp_d]
    rfl

private noncomputable def nativeUnderlyingIso (A : OrdinaryAlgebras)
    (N : ShuffleAlgebraFunctor ℤ) (C : ConstantRingSource A N)
    (J : OrdinaryModuleSource A N C)
    (P : MathlibExt.CategoryTheory.DGQuasiFunctorModels.RightModule ℤ (ringCategory A N)) :
    (integerComplex A).obj (nativeComplex A N C J P) ≅ ringValue A N P := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · let e : ((integerComplex A).obj (nativeComplex A N C J P)).X i ≃+
        (ringValue A N P).X i :=
      { toFun := fun m => m
        invFun := fun m => m
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
    exact e.toIntLinearEquiv.toModuleIso
  · intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

private noncomputable def moduleCycle (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ)
    (C : ConstantRingSource A N)
    (M P : MathlibExt.CategoryTheory.DGQuasiFunctorModels.RightModule ℤ (ringCategory A N))
    (f : ringValue A N M ⟶ ringValue A N P)
    (hf : letI := (ringCategory A N).dg;
      ∀ (r : A) (i : ℤ) (m : (ringValue A N M).X i),
        (f.f i).hom
          (((M.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
            Cochain _ _ 0).v i i (add_zero i)).hom m) =
        (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
          Cochain _ _ 0).v i i (add_zero i)).hom ((f.f i).hom m))) :
    letI := (ringCategory A N).dg
    dgCycles ℤ M P := by
  let _ := (ringCategory A N).dg
  let η : ∀ x : (ringCategory A N)ᵒᵖ,
      DGHom ℤ 0 (M.toEnrichedFunctor.obj x) (P.toEnrichedFunctor.obj x) := fun x => by
    rcases x with ⟨x⟩
    cases x
    exact Cochain.ofHom f
  have hn : DGFunctor.IsNatural (F := M) (G := P) η := by
    apply DGFunctor.isNatural_def.2
    intro X Y p n a h₁ h₂
    rcases X with ⟨X⟩
    cases X
    rcases Y with ⟨Y⟩
    cases Y
    by_cases hp : p = 0
    · subst p
      have hn : n = 0 := by omega
      subst n
      have ha : a = scalar A N C (C.degree_zero.hom.hom a) := by
        symm
        change (C.degree_zero.hom ≫ C.degree_zero.inv).hom a = a
        rw [C.degree_zero.hom_inv_id]
        rfl
      rw [ha]
      apply Cochain.ext₀
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      simpa only [η, dgComp_linearHomComplex, zero_mul, Int.negOnePow_zero,
        one_smul, add_zero, zero_add, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
        ModuleCat.hom_comp, LinearMap.comp_apply] using! hf (C.degree_zero.hom.hom a) i m
    · have hz : a = 0 := @Subsingleton.elim _
        (ModuleCat.isZero_iff_subsingleton.1 (C.off_zero p hp)) _ _
      simp only [hz, map_zero, zero_dgComp, dgComp_zero, mul_zero, Int.negOnePow_zero, one_smul]
  have hm : η ∈ DGFunctor.natTransSubmodule M P 0 := by
    rw [DGFunctor.mem_natTransSubmodule]
    exact hn
  refine ⟨(DGFunctor.dgHomEquiv ℤ M P 0).symm ⟨η, hm⟩, ?_⟩
  apply (mem_dgCycles ℤ).2
  apply DGFunctor.dgHom_ext
  intro x
  rcases x with ⟨x⟩
  cases x
  rw [DGFunctor.dgApp_dgDifferential, DGFunctor.dgApp_dgHomEquiv_symm_apply,
    map_zero, dgDifferential_linearHomComplex]
  simpa only [η] using! (δ_ofHom f (p := 1))

private noncomputable def moduleHomotopyIso (A : OrdinaryAlgebras)
    (N : ShuffleAlgebraFunctor ℤ) (C : ConstantRingSource A N)
    (M P : MathlibExt.CategoryTheory.DGQuasiFunctorModels.RightModule ℤ (ringCategory A N))
    (e : ringValue A N M ≅ ringValue A N P)
    (he : letI := (ringCategory A N).dg;
      ∀ (r : A) (i : ℤ) (m : (ringValue A N M).X i),
        (e.hom.f i).hom
          (((M.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
            Cochain _ _ 0).v i i (add_zero i)).hom m) =
        (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
          Cochain _ _ 0).v i i (add_zero i)).hom ((e.hom.f i).hom m))) :
    letI := (ringCategory A N).dg
    DGHomotopyCategory.of ℤ M ≅ DGHomotopyCategory.of ℤ P := by
  let _ := (ringCategory A N).dg
  have hi (r : A) (i : ℤ) (m : (ringValue A N P).X i) :
      (e.inv.f i).hom
        (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
          Cochain _ _ 0).v i i (add_zero i)).hom m) =
      (((M.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
        Cochain _ _ 0).v i i (add_zero i)).hom ((e.inv.f i).hom m)) := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.f i)).1
    have hr (v : (ringValue A N P).X i) : (e.hom.f i).hom ((e.inv.f i).hom v) = v := by
      change ((e.inv ≫ e.hom).f i).hom v = v
      rw [e.inv_hom_id]
      rfl
    simpa only [hr] using (he r i ((e.inv.f i).hom m)).symm
  let u := moduleCycle A N C M P e.hom he
  let v := moduleCycle A N C P M e.inv hi
  have huv : dgComp ℤ u.1 v.1 (add_zero 0) = dgId ℤ M := by
    apply DGFunctor.dgHom_ext
    intro x
    rcases x with ⟨x⟩
    cases x
    simp only [u, v, DGFunctor.dgApp_dgComp, DGFunctor.dgApp_dgId,
      moduleCycle, DGFunctor.dgApp_dgHomEquiv_symm_apply]
    rw [dgComp_linearHomComplex, zero_mul, Int.negOnePow_zero, one_smul,
      ← Cochain.ofHom_comp, e.hom_inv_id, dgId_linearHomComplex]
  have hvu : dgComp ℤ v.1 u.1 (add_zero 0) = dgId ℤ P := by
    apply DGFunctor.dgHom_ext
    intro x
    rcases x with ⟨x⟩
    cases x
    simp only [u, v, DGFunctor.dgApp_dgComp, DGFunctor.dgApp_dgId,
      moduleCycle, DGFunctor.dgApp_dgHomEquiv_symm_apply]
    rw [dgComp_linearHomComplex, zero_mul, Int.negOnePow_zero, one_smul,
      ← Cochain.ofHom_comp, e.inv_hom_id, dgId_linearHomComplex]
  exact
    { hom := DGHomotopyCategory.homOf ℤ u.1 u.2
      inv := DGHomotopyCategory.homOf ℤ v.1 v.2
      hom_inv_id := DGHomotopyCategory.homOf_comp_eq_id_of_dgComp_eq_dgId ℤ u.2 v.2 huv
      inv_hom_id := DGHomotopyCategory.homOf_comp_eq_id_of_dgComp_eq_dgId ℤ v.2 u.2 hvu }

/-- This all-complex native source comparison is a whole DG quasi-equivalence. -/
theorem ordinary_constant_module_quasi_equivalence (A : OrdinaryAlgebras)
    (N : ShuffleAlgebraFunctor ℤ) (C : ConstantRingSource A N) (J : OrdinaryModuleSource A N C) :
    letI := moduleDG A
    J.functor.IsQuasiEquivalence
    := by
  let _ := moduleDG A
  apply (EnrichedFunctor.isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj _).2
  constructor
  · apply EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
    intro F G
    exact hom_map_isIso A N C J F G
  · constructor
    intro Y
    let P := DGHomotopyCategory.underlying ℤ Y
    let F := nativeComplex A N C J P
    have e : DGHomotopyCategory.of ℤ (J.functor.obj F) ≅ DGHomotopyCategory.of ℤ P := by
      apply moduleHomotopyIso A N C (J.functor.obj F) P
        ((J.object F).trans (nativeUnderlyingIso A N C J P))
      intro r i m
      change ((J.object F).hom.f i).hom
          (((((J.functor.obj F).toEnrichedFunctor.dgMap 0 (scalar A N C r) :
            Cochain _ _ 0).v i i (add_zero i)).hom m)) =
        (((P.toEnrichedFunctor.dgMap 0 (scalar A N C r) :
          Cochain _ _ 0).v i i (add_zero i)).hom (((J.object F).hom.f i).hom m))
      rw [J.action]
      rfl
    refine ⟨DGHomotopyCategory.of ℤ F, ⟨?_⟩⟩
    simpa only [EnrichedFunctor.mapDGHomotopyCategory_obj_of, P,
      DGHomotopyCategory.of_underlying] using e
end MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
