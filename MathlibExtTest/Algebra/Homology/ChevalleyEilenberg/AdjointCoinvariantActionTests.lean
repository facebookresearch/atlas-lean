/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.AdjointCoinvariantNaturality
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.RightAdjointCoefficients
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CommutingScalars
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public meta import Mathlib.Tactic.NormNum

/-!
# Nonzero adjoint actions and coinvariants of integer matrices

The commutator algebra of two-by-two integer matrices acts nontrivially in exterior degree one.
Its adjoint coinvariant projection kills a nonzero diagonal commutator, while trace detects the
identity class as `2`. Negative transpose induces a nonidentity map of coinvariant coalgebras.
The descended coproduct is nonzero on the identity class, as its counit law requires. A commuting
scalar action on the coefficient complex is detected on a genuine pure tensor.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ChevalleyEilenberg
open scoped TensorProduct ModuleCat.UniverseTensor

namespace MathlibExtTest.AdjointCoinvariantAction

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
local instance : LieRing Mat := LieRing.ofAssociativeRing
local instance : LieAlgebra ℤ Mat := LieAlgebra.ofAssociativeAlgebra
local instance : LieRingModule Mat Mat := lieRingSelfModule
local instance : LieModule ℤ Mat Mat := lieAlgebraSelfModule
local instance : HasFiniteBiproducts (ModuleCat ℤ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat ℤ)

private def e01 : Mat := !![0, 1; 0, 0]
private def e10 : Mat := !![0, 0; 1, 0]
private def diagonal : Mat := !![1, 0; 0, -1]
private def oneWord (m : Mat) : ⋀[ℤ]^1 Mat := exteriorPower.ιMulti ℤ 1 (fun _ => m)
private abbrev incl : Mat →ₗ⁅ℤ⁆ Mat := LieHom.id
private abbrev Q := adjointCoinvariantComplex ℤ Mat incl
private abbrev q := adjointCoinvariantProjection ℤ Mat incl
private abbrev relations := adjointDegreeSpan ℤ Mat incl 1
private abbrev coordinate := adjointCoinvariantCoordinateIso ℤ Mat incl 1

private lemma bracket_pair : ⁅e01, e10⁆ = diagonal := by
  change e01 * e10 - e10 * e01 = diagonal
  decide
private lemma action_read (x y : Mat) :
    exteriorPower.oneEquiv ℤ Mat (degreeAdjointAction ℤ Mat 1 x (oneWord y)) = ⁅x, y⁆ := by
  simp [degreeAdjointAction_pure, oneWord]
private lemma left_action : degreeAdjointAction ℤ Mat 1 e01 (oneWord e10) =
    oneWord diagonal := by
  apply (exteriorPower.oneEquiv ℤ Mat).injective
  rw [action_read, bracket_pair]
  simp [oneWord]
private lemma trace_bracket (x y : Mat) : Matrix.trace ⁅x, y⁆ = 0 := by
  change Matrix.trace (x * y - y * x) = 0
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
private def traceOne : (⋀[ℤ]^1 Mat) →ₗ[ℤ] ℤ :=
  (Matrix.traceLinearMap (Fin 2) ℤ ℤ).comp (exteriorPower.oneEquiv ℤ Mat).toLinearMap
private lemma trace_kills_relations : relations ≤ LinearMap.ker traceOne := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, a, rfl⟩
  change traceOne (degreeAdjointAction ℤ Mat 1 x a) = 0
  have ha : oneWord (exteriorPower.oneEquiv ℤ Mat a) = a := by
    apply (exteriorPower.oneEquiv ℤ Mat).injective
    simp [oneWord]
  rw [← ha]
  change Matrix.trace (exteriorPower.oneEquiv ℤ Mat
    (degreeAdjointAction ℤ Mat 1 x (oneWord (exteriorPower.oneEquiv ℤ Mat a)))) = 0
  rw [action_read, trace_bracket]
private def quotientTrace : adjointCoinvariantModule ℤ Mat incl 1 →ₗ[ℤ] ℤ :=
  relations.liftQ traceOne trace_kills_relations
private def readQ : Q.X 1 →ₗ[ℤ] ℤ := quotientTrace.comp coordinate.hom.hom
private lemma readQ_projection (m : Mat) : readQ ((q.f 1).hom (oneWord m)) =
    Matrix.trace m := by
  have h := congrArg (fun f => f.hom (oneWord m))
    (adjointCoinvariantProjection_coordinates ℤ Mat incl 1)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at h
  change quotientTrace (coordinate.hom.hom ((q.f 1).hom (oneWord m))) = Matrix.trace m
  rw [h]
  change traceOne (oneWord m) = Matrix.trace m
  simp [traceOne, oneWord]
private def identityClass : Q.X 1 := (q.f 1).hom (oneWord (1 : Mat))
private lemma identity_trace : readQ identityClass = 2 := by
  rw [identityClass, readQ_projection]
  norm_num
private lemma identity_ne_zero : identityClass ≠ 0 := by
  intro hz
  have h := identity_trace.symm.trans ((congrArg readQ hz).trans readQ.map_zero)
  norm_num at h

example : degreeAdjointAction ℤ Mat 1 e01 (oneWord e10) = oneWord diagonal := left_action
example : degreeAdjointAction ℤ Mat 1 e01 (oneWord e10) ≠ 0 := by
  rw [left_action]
  intro hz
  have h := congrArg (fun a => exteriorPower.oneEquiv ℤ Mat a 0 0) hz
  norm_num [oneWord, diagonal] at h
example : (rightAdjointCoefficients ℤ Mat incl 1).action e01 (oneWord e10) =
    -oneWord diagonal := by
  rw [rightAdjointCoefficients_action]
  change -degreeAdjointAction ℤ Mat 1 e01 (oneWord e10) = -oneWord diagonal
  rw [left_action]
example : (q.f 1).hom (oneWord diagonal) = 0 := by
  apply LinearMap.mem_ker.mp
  rw [adjointCoinvariantProjection_ker ℤ Mat incl 1, ← left_action]
  exact Submodule.subset_span ⟨e01, oneWord e10, rfl⟩
example : readQ identityClass = 2 := identity_trace
example : identityClass ≠ 0 := identity_ne_zero

private def flip : Mat →ₗ⁅ℤ⁆ Mat where
  toLinearMap := -(Matrix.transposeLinearEquiv (Fin 2) (Fin 2) ℤ ℤ).toLinearMap
  map_lie' := by
    intro a b
    change -(a * b - b * a)ᵀ = (-aᵀ) * (-bᵀ) - (-bᵀ) * (-aᵀ)
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [neg_mul_neg, neg_sub]
private def flipQ : Q ⟶ Q :=
  adjointCoinvariantMap ℤ Mat incl incl flip flip (by ext a; rfl)
private lemma flip_trace : readQ ((flipQ.f 1).hom identityClass) = -2 := by
  have h := adjointCoinvariantMap_pure ℤ Mat incl incl flip flip (by ext a; rfl)
    1 (fun _ => (1 : Mat))
  change readQ ((flipQ.f 1).hom ((q.f 1).hom (oneWord (1 : Mat)))) = -2
  rw [h]
  change readQ ((q.f 1).hom (oneWord (flip (1 : Mat)))) = -2
  rw [readQ_projection]
  norm_num [flip]
example : readQ ((flipQ.f 1).hom identityClass) = -2 := flip_trace
example : flipQ ≠ 𝟙 Q := by
  intro hz
  have h := congrArg (fun f : Q ⟶ Q => readQ ((f.f 1).hom identityClass)) hz
  rw [flip_trace] at h
  change (-2 : ℤ) = readQ identityClass at h
  rw [identity_trace] at h
  norm_num at h

example : ((adjointCoinvariantComul ℤ Mat incl).f 1).hom identityClass ≠ 0 := by
  letI : ComonObj Q := adjointCoinvariantComonObj ℤ Mat incl
  let T := HomologicalComplex.tensorHom (adjointCoinvariantCounit ℤ Mat incl) (𝟙 Q)
  have h : adjointCoinvariantComul ℤ Mat incl ≫ T = (λ_ Q).inv := by
    simpa only [Category.id_comp] using ComonObj.counit_comul_hom (𝟙 Q)
  intro hz
  have hp := congrArg (fun f => (f.f 1).hom identityClass) h
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  let e := (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) 1).mapIso (λ_ Q)
  have he : e.inv.hom identityClass = 0 :=
    hp.symm.trans ((congrArg (T.f 1).hom hz).trans (T.f 1).hom.map_zero)
  exact identity_ne_zero (e.symm.toLinearEquiv.injective
    (he.trans e.inv.hom.map_zero.symm))

private abbrev X := LieModuleCat.of ℤ Mat Mat
private def rho : ℤ →+* Module.End ℤ X := (Algebra.lsmul (A := ℤ) ℤ ℤ X).toRingHom
private lemma rho_commutes (r : ℤ) (x : Mat) (m : X) : rho r ⁅x, m⁆ = ⁅x, rho r m⁆ := by
  change r • ⁅x, m⁆ = ⁅x, r • m⁆
  rw [lie_smul]
private def entry (i j : Fin 2) : Mat →ₗ[ℤ] ℤ := (LinearMap.proj j).comp (LinearMap.proj i)
private def readAction : ((⋀[ℤ]^1 Mat) ⊗[ℤ] Mat) →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map
    ((entry 0 1).comp (exteriorPower.oneEquiv ℤ Mat).toLinearMap) (entry 1 0))
example : readAction (coefficientDegreeRingAction ℤ Mat X rho rho_commutes 1 2
    (oneWord e01 ⊗ₜ[ℤ] e10)) = 2 := by
  have h : coefficientDegreeRingAction ℤ Mat X rho rho_commutes 1 2
      (oneWord e01 ⊗ₜ[ℤ] e10) = oneWord e01 ⊗ₜ[ℤ] (2 • e10) :=
    coefficientComplexRingAction_f_tmul ℤ Mat X rho rho_commutes 2 1 (oneWord e01) e10
  rw [h]
  norm_num [readAction, oneWord, entry, e01, e10, TensorProduct.map_tmul]

end MathlibExtTest.AdjointCoinvariantAction
