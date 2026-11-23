/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeLieJetFamilies
public import MathlibExt.AlgebraicGeometry.CameralChevalleyModels
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Native reductive-group and normalizer source data

The reductive Lie algebra is the actual identity-derivation realization
of the specified connected smooth affine group. Its Cartan inclusion is
the derivative of the actual torus inclusion on every coefficient
algebra. Roots are exactly its nonzero torus weights.

The normalizer represents actual conjugation preserving the embedded
torus on every test scheme. Its Weyl quotient is the actual torus torsor
over the constant finite group scheme, whose points are locally constant
maps rather than a single discrete label on each test scheme.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Section0.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralReductiveSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ExpansionParameterModels CameralTorusBands RegularCentralizerAffineModels
open SchemeLieJetFamilies
open scoped TensorProduct BigOperators

variable {k : Type} [Field k] {r : ℕ}
  (G : Over (Spec (.of k))) [GrpObj G]
  (V : Type) [LieRing V] [LieAlgebra k V] [FiniteDimensional k V]
  (L : AffineGroupLieModels.LieModel G V)
  (J : TangentFamilies G V L) (D : AdjointFamilies G V L J)
  (T : TorusTheory k r) (Gm : TorusTheory k 1)
  (W : Type) [Group W] [Fintype W] (R : Roots T Gm W)

def cartanAt (c : (Fin r → k) →ₗ[k] V) (A : CommAlgCat.{0} k) (v : Fin r → A) :
    LieAt V A := ∑ i, v i ⊗ₜ[k] c (Pi.single i 1)

/-- The value of the character `χ` at an `A`-point `t` of the torus. -/
def weightValue (A : CommAlgCat.{0} k) (t : affine A ⟶ torusScheme k r) (χ : Fin r → ℤ) : A :=
  (Scheme.ΓSpecIso (.of A)).hom.hom
    ((∏ i, (T.units (affine A) t i) ^ χ i : Γ(Spec (.of A), ⊤)ˣ) : Γ(Spec (.of A), ⊤))

/-- The weight space of `χ`: the torus acts on `1 ⊗ v` through `χ` at every affine test point,
not only at rational points (over a finite field the rational points of a split torus do not
detect the weights). -/
def weightSpace (embedding : torusScheme k r ⟶ G) (χ : Fin r → ℤ) : Submodule k V where
  carrier := {v | ∀ (A : CommAlgCat.{0} k) (t : affine A ⟶ torusScheme k r),
    D.adjoint A (t ≫ embedding) ((1 : A) ⊗ₜ[k] v) = weightValue T A t χ • ((1 : A) ⊗ₜ[k] v)}
  zero_mem' A t := by simp
  add_mem' hv hw A t := by rw [TensorProduct.tmul_add, map_add, hv A t, hw A t, smul_add]
  smul_mem' a v hv A t := by
    have h := (D.adjoint A (t ≫ embedding)).toLinearMap.map_smul_of_tower a ((1 : A) ⊗ₜ[k] v)
    rw [LinearEquiv.coe_coe] at h
    rw [TensorProduct.tmul_smul, h, hv A t, smul_comm]

structure Source where
  [connected : ConnectedSpace G.left]
  [smooth : Smooth G.hom]
  [finiteType : LocallyOfFiniteType G.hom]
  [reductive : LieAlgebra.HasCentralRadical k V]
  torus : torusScheme k r ⟶ G
  [torus_mono : Mono torus]
  torus_hom : letI := T.group; IsMonHom torus
  cartan : (Fin r → k) →ₗ[k] V
  cartan_injective : Function.Injective cartan
  cartan_abelian : ∀ v w : Fin r → k, ⁅cartan v, cartan w⁆ = 0
  torus_derivative : ∀ (A : CommAlgCat.{0} k) (v : Fin r → A),
    jetPoint G V L J A (cartanAt V cartan A v) =
      CameralChevalleyModels.firstOrderPoint T A v ≫ torus
  cartan_centralizer : ∀ v : V,
    (∀ w : Fin r → k, ⁅cartan w, v⁆ = 0) ↔ v ∈ LinearMap.range cartan
  roots_distinct : Function.Injective R.exponent
  roots_nonzero : ∀ i : Fin R.count, R.exponent i ≠ 0
  root_rank : ∀ i : Fin R.count,
    Module.finrank k (weightSpace G V L J D T torus (R.exponent i)) = 1
  all_roots : ∀ χ : Fin r → ℤ, χ ≠ 0 →
    weightSpace G V L J D T torus χ ≠ ⊥ ↔ ∃ i : Fin R.count, R.exponent i = χ

def Normalizes (embedding : torusScheme k r ⟶ G)
    {U : Over (Spec (.of k))} (g : U ⟶ G) : Prop :=
  ∃ f h : U ⊗ torusScheme k r ⟶ torusScheme k r,
    conjugate G (fst U (torusScheme k r) ≫ g)
      (snd U (torusScheme k r) ≫ embedding) = f ≫ embedding ∧
    conjugate G (fst U (torusScheme k r) ≫ g ≫ ι[G])
      (snd U (torusScheme k r) ≫ embedding) = h ≫ embedding

structure ConstantWeyl where
  scheme : Over (Spec (.of k))
  [group : GrpObj scheme]
  [finite : IsFinite scheme.hom]
  [etale : Etale scheme.hom]
  points : ∀ U : Over (Spec (.of k)), (U ⟶ scheme) ≃ LocallyConstant U.left W
  identity : ∀ (U : Over (Spec (.of k))) (x : U.left),
    points U (toUnit U ≫ η[scheme]) x = 1
  multiply : ∀ (U : Over (Spec (.of k))) (f g : U ⟶ scheme) (x : U.left),
    points U (CartesianMonoidalCategory.lift f g ≫ μ[scheme]) x =
      points U f x * points U g x
  naturality : ∀ {U U' : Over (Spec (.of k))} (f : U' ⟶ U) (g : U ⟶ scheme) (x : U'.left),
    points U' (f ≫ g) x = points U g (f.left x)

attribute [instance] ConstantWeyl.group ConstantWeyl.finite ConstantWeyl.etale

structure Normalizer (S : Source G V L J D T Gm W R) (Q : ConstantWeyl (k := k) W) where
  scheme : Over (Spec (.of k))
  [group : GrpObj scheme]
  inclusion : scheme ⟶ G
  [mono : Mono inclusion]
  [hom : IsMonHom inclusion]
  points : ∀ U : Over (Spec (.of k)), (U ⟶ scheme) ≃
    {g : U ⟶ G // Normalizes G S.torus g}
  points_normalized : ∀ (U : Over (Spec (.of k))) (n : U ⟶ scheme),
    (points U n).val = n ≫ inclusion
  torus : torusScheme k r ⟶ scheme
  torus_normalized : torus ≫ inclusion = S.torus
  quotient : scheme ⟶ Q.scheme
  [quotient_hom : IsMonHom quotient]
  torsor : letI := T.group; GroupTorsorGeometry.Torsor (torusScheme k r) Q.scheme
  total : letI := T.group; torsor.total ≅ scheme
  projection : letI := T.group; total.hom ≫ quotient = torsor.projection
  action : letI := T.group
    γ[torusScheme k r,torsor.total] ≫ total.hom =
      tensorHom torus total.hom ≫ μ[scheme]
  weyl_action : ∀ (U : Over (Spec (.of k))) (n : U ⟶ scheme) (w : W),
    (∀ x : U.left, Q.points U (n ≫ quotient) x = w) →
      conjugate G (fst U (torusScheme k r) ≫ n ≫ inclusion)
        (snd U (torusScheme k r) ≫ S.torus) =
      snd U (torusScheme k r) ≫ (R.action w).asIso.hom ≫ S.torus

end MathlibExt.AlgebraicGeometry.CameralReductiveSources
