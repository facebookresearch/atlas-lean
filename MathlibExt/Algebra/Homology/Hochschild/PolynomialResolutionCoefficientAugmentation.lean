/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionTensorPowers
public import MathlibExt.Algebra.Category.ModuleCat.FlatTargetResolutionTensor
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Polynomial tensor-power resolutions with arbitrary coefficients

Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. Each term `P_p` of
the canonical polynomial resolution has a monomial basis over `k`. For every `q : ℕ`, the
finite tensor power `P_p^{⊗ q}` therefore has a tensor-monomial basis, so the alternating-face
complex of the tensor-power diagram has projective terms.

If `B` is flat over `k`, this complex with its augmentation is a projective resolution of
`B^{⊗ q}`, and the target tensor power is flat. For an arbitrary `M : ModuleCat.{w} k`, the
augmented simplicial diagram `M ⊗_k P^{⊗ q}` consequently has a quasi-isomorphism to `M ⊗_k
B^{⊗ q}` concentrated in chain degree zero. Its carrier is represented in universe `max u v
w`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

open CategoryTheory.SimplicialObject.ModuleTensor

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `p : ℕ`, put `V_p =
(CommAlgCat.polynomialPower k p).obj B`. The `k`-module `(additiveDiagram k B).obj (op ⦋p⦌)`
has a basis indexed by `V_p →₀ ℕ`, obtained from polynomial monomials through the canonical
isomorphism of the degree-`p` resolution algebra with the polynomial algebra in `V_p`. -/
def additiveDiagramMonomialBasis (p : ℕ) :
    Module.Basis (((CommAlgCat.polynomialPower k p).obj B) →₀ ℕ) k
      ((additiveDiagram k B).obj (op ⦋p⦌)) := by
  let I : Type (max u v) := (CommAlgCat.polynomialPower k p).obj B
  let b : Module.Basis (I →₀ ℕ) k (MvPolynomial I k) := MvPolynomial.basisMonomials I k
  let e := (CommAlgCat.algEquivOfIso (CommAlgCat.polynomialResolutionObjIso k B p)).toLinearEquiv
  exact b.map e.symm

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `p : ℕ`, the module
`(additiveDiagram k B).obj (op ⦋p⦌)` is free over `k`. A basis is
`additiveDiagramMonomialBasis k B p`, indexed by finite-support monomial exponents on the
preceding polynomial-power carrier. -/
theorem additiveDiagram_free (p : ℕ) : Module.Free k ((additiveDiagram k B).obj (op ⦋p⦌)) :=
  Module.Free.of_basis (additiveDiagramMonomialBasis k B p)

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `q, p : ℕ`. Put `V_p
= (CommAlgCat.polynomialPower k p).obj B`. The degree-`p` term of `tensorPowerDiagram k B q`
has a `k`-basis indexed by `Fin q → (V_p →₀ ℕ)`, the ordered `q`-tuples of monomial basis
indices. The construction also includes `q=0`. -/
def tensorPowerMonomialBasis (q p : ℕ) :
    Module.Basis (Fin q → (((CommAlgCat.polynomialPower k p).obj B) →₀ ℕ)) k
      ((tensorPowerDiagram k B q).obj (op ⦋p⦌)) :=
  _root_.Basis.piTensorProduct (fun _ : Fin q => additiveDiagramMonomialBasis k B p)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q, p : ℕ`, the object
`((alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (tensorPowerDiagram k B q)).X p`
is projective in `ModuleCat.{max u v} k`. Its tensor-monomial basis makes its underlying `k`-module free. -/
theorem tensorPowerAlternating_projective (q p : ℕ) :
    Projective (((alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (tensorPowerDiagram k B q)).X p) :=
  ModuleCat.projective_of_free (tensorPowerMonomialBasis k B q p)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`,
`tensorPowerAugmented k B q` has simplicial part `tensorPowerDiagram k B q`, augmentation
object `(powerFunctor k q).obj (coefficientModule k B) = B^{⊗ q}`, and augmentation
`tensorPowerAugmentation k B q`, which applies the resolution augmentation to every tensor
factor. -/
def tensorPowerAugmented (q : ℕ) : SimplicialObject.Augmented (ModuleCat.{max u v} k) where
  left := tensorPowerDiagram k B q
  right := (powerFunctor k q).obj (coefficientModule k B)
  hom := tensorPowerAugmentation k B q

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be flat over `k`. For every `q : ℕ`,
`QuasiIso (AlternatingFaceMapComplex.ε.app (tensorPowerAugmented k B q))`.
The map augments the alternating-face complex of the polynomial tensor-power diagram to `B^{⊗ q}` concentrated in chain
degree zero. -/
theorem tensorPowerAlternatingAugmentation_quasiIso [Module.Flat k B] (q : ℕ) :
    _root_.QuasiIso (AlternatingFaceMapComplex.ε.app (tensorPowerAugmented k B q)) := by
  let X := tensorPowerAugmented k B q
  let Y := (SimplicialObject.Augmented.const (C := ModuleCat.{max u v} k)).obj X.right
  let _ : _root_.QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map X.hom) :=
    tensorPowerAugmentation_quasiIso k B q
  let _ : _root_.QuasiIso (AlternatingFaceMapComplex.ε.app Y) :=
    (SimplicialObject.Augmented.constantRightExtraDegeneracy X.right).quasiIso_augmentation
  have h := AlternatingFaceMapComplex.ε.naturality (SimplicialObject.Augmented.augmentationToConstant X)
  change (alternatingFaceMapComplex (ModuleCat.{max u v} k)).map X.hom ≫
      AlternatingFaceMapComplex.ε.app Y =
    AlternatingFaceMapComplex.ε.app X ≫ (ChainComplex.single₀ (ModuleCat.{max u v} k)).map (𝟙 X.right) at h
  let α : (alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj X.left ⟶
      (alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj Y.left :=
    (alternatingFaceMapComplex (ModuleCat.{max u v} k)).map X.hom
  let β : (alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj Y.left ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} k)).obj X.right := AlternatingFaceMapComplex.ε.app Y
  let γ := AlternatingFaceMapComplex.ε.app X
  have h' : α ≫ β = γ := h.trans
    ((congrArg (fun t => γ ≫ t) ((ChainComplex.single₀ (ModuleCat.{max u v} k)).map_id X.right)).trans
      (Category.comp_id γ))
  let _ : _root_.QuasiIso α := tensorPowerAugmentation_quasiIso k B q
  let _ : _root_.QuasiIso β :=
    (SimplicialObject.Augmented.constantRightExtraDegeneracy X.right).quasiIso_augmentation
  have hq : _root_.QuasiIso (α ≫ β) := inferInstance
  change _root_.QuasiIso γ
  exact h' ▸ hq

/-- For a commutative ring `k : Type u`, a `k`-flat algebra `B : CommAlgCat.{max u v} k`, and `q :
ℕ`, the projective resolution of `(powerFunctor k q).obj (coefficientModule k B)` has complex
`(alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (tensorPowerDiagram k B q)` and
augmentation `AlternatingFaceMapComplex.ε.app (tensorPowerAugmented k B q)`. Projectivity is
supplied by the tensor-monomial bases and the augmentation is a quasi-isomorphism. -/
def tensorPowerProjectiveResolution [Module.Flat k B] (q : ℕ) :
    ProjectiveResolution ((powerFunctor k q).obj (coefficientModule k B)) where
  complex := (alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (tensorPowerDiagram k B q)
  π := AlternatingFaceMapComplex.ε.app (tensorPowerAugmented k B q)
  projective := tensorPowerAlternating_projective k B q
  quasiIso := tensorPowerAlternatingAugmentation_quasiIso k B q

/-- For a commutative ring `k : Type u`, a `k`-flat algebra `B : CommAlgCat.{max u v} k`, and `q : ℕ`, the resolution
augmentation satisfies
`((tensorPowerProjectiveResolution k B q).π).f 0 = (tensorPowerAugmentation k B q).app (op ⦋0⦌)`.
Its degree-zero component is the tensor power of the degree-zero polynomial-resolution augmentation. -/
theorem tensorPowerProjectiveResolution_π_f_zero [Module.Flat k B] (q : ℕ) :
    ((tensorPowerProjectiveResolution k B q).π).f 0 = (tensorPowerAugmentation k B q).app (op ⦋0⦌) :=
  AlternatingFaceMapComplex.ε_app_f_zero (tensorPowerAugmented k B q)

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k` be `k`-flat, and `q : ℕ`. For `a : Fin q →
(additiveDiagram k B).obj (op ⦋0⦌)`,
`(((tensorPowerProjectiveResolution k B q).π).f 0).hom (PiTensorProduct.tprod k a) = PiTensorProduct.tprod k (fun j =>
((additiveAugmentation k B).app (op ⦋0⦌)).hom (a j))`.
Each monomial-tensor factor is sent by the degree-zero resolution augmentation. -/
theorem tensorPowerProjectiveResolution_π_f_zero_tprod [Module.Flat k B] (q : ℕ)
    (a : Fin q → (additiveDiagram k B).obj (op ⦋0⦌)) :
    (((tensorPowerProjectiveResolution k B q).π).f 0).hom (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun j => ((additiveAugmentation k B).app (op ⦋0⦌)).hom (a j)) := by
  have hπ := tensorPowerProjectiveResolution_π_f_zero k B q
  exact (congrArg (fun m => m.hom (PiTensorProduct.tprod k a)) hπ).trans
    (tensorPowerAugmentation_tprod k B q (op ⦋0⦌) a)

variable (M : ModuleCat.{w} k)

/-- For a commutative ring `k : Type u` and `M : ModuleCat.{w} k`, the functor
`arbitraryCoefficientTensorFunctor k M` tensors on the left by `M`. Its domain is
`ModuleCat.{max u v} k` and its target is `ModuleCat.{max u v w} k`, using
`ModuleCat.tensorBifunctorAt` to represent the tensor carriers in that target universe. -/
abbrev arbitraryCoefficientTensorFunctor : ModuleCat.{max u v} k ⥤ ModuleCat.{max u v w} k :=
  (ModuleCat.tensorBifunctorAt.{u, w, max u v} k).obj M

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, `M : ModuleCat.{w} k`,
and `q : ℕ`. The simplicial module `arbitraryCoefficientTensorDiagram k B M q` is
`tensorPowerDiagram k B q ⋙ arbitraryCoefficientTensorFunctor k M`. Its degree-`p` term is the
coefficient-first tensor `M ⊗_k P_p^{⊗ q}`, represented in `ModuleCat.{max u v w} k`. -/
def arbitraryCoefficientTensorDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v w} k) :=
  tensorPowerDiagram k B q ⋙ arbitraryCoefficientTensorFunctor k M

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, `M : ModuleCat.{w} k`, and
`q : ℕ`, the simplicial augmentation goes from `arbitraryCoefficientTensorDiagram k B M q` to
the constant module `M ⊗_k B^{⊗ q}` in universe `max u v w`. In each simplicial degree it
applies `arbitraryCoefficientTensorFunctor k M` to `tensorPowerAugmentation k B q`. -/
def arbitraryCoefficientTensorAugmentation (q : ℕ) : arbitraryCoefficientTensorDiagram k B M q ⟶
    (SimplicialObject.const (ModuleCat.{max u v w} k)).obj
      ((arbitraryCoefficientTensorFunctor k M).obj ((powerFunctor k q).obj (coefficientModule k B))) :=
  { app i := (arbitraryCoefficientTensorFunctor k M).map ((tensorPowerAugmentation k B q).app i)
    naturality {i j} θ := by
      let F := arbitraryCoefficientTensorFunctor k M
      have h : (tensorPowerDiagram k B q).map θ ≫ (tensorPowerAugmentation k B q).app j =
          (tensorPowerAugmentation k B q).app i :=
        ((tensorPowerAugmentation k B q).naturality θ).trans (Category.comp_id _)
      change F.map ((tensorPowerDiagram k B q).map θ) ≫ F.map ((tensorPowerAugmentation k B q).app j) =
        F.map ((tensorPowerAugmentation k B q).app i) ≫ 𝟙 _
      exact (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (Category.comp_id _).symm) }

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, `M : ModuleCat.{w} k`, `q : ℕ`, and `i :
SimplexCategoryᵒᵖ`. As a morphism from the coefficient tensor of `(tensorPowerDiagram k B q).obj i` to that of `B^{⊗
q}`,
`(arbitraryCoefficientTensorAugmentation k B M q).app i = (arbitraryCoefficientTensorFunctor k M).map
((tensorPowerAugmentation k B q).app i)`. -/
theorem arbitraryCoefficientTensorAugmentation_app (q : ℕ) (i : SimplexCategoryᵒᵖ) :
    @Eq ((arbitraryCoefficientTensorFunctor k M).obj ((tensorPowerDiagram k B q).obj i) ⟶
      (arbitraryCoefficientTensorFunctor k M).obj ((powerFunctor k q).obj (coefficientModule k B)))
      ((arbitraryCoefficientTensorAugmentation k B M q).app i)
      ((arbitraryCoefficientTensorFunctor k M).map ((tensorPowerAugmentation k B q).app i)) := by
  rfl

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, `M : ModuleCat.{w} k`, and
`q : ℕ`, `arbitraryCoefficientTensorAugmented k B M q` has simplicial part
`arbitraryCoefficientTensorDiagram k B M q`, augmentation object `M ⊗_k B^{⊗ q}`, and map
`arbitraryCoefficientTensorAugmentation k B M q`, all represented in `ModuleCat.{max u v w}
k`. -/
def arbitraryCoefficientTensorAugmented (q : ℕ) : SimplicialObject.Augmented (ModuleCat.{max u v w} k) where
  left := arbitraryCoefficientTensorDiagram k B M q
  right := (arbitraryCoefficientTensorFunctor k M).obj ((powerFunctor k q).obj (coefficientModule k B))
  hom := arbitraryCoefficientTensorAugmentation k B M q

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be flat over `k`. For
every `q : ℕ`, the target `(powerFunctor k q).obj (coefficientModule k B)`, representing `B^{⊗
q}`, is flat as a `k`-module. -/
theorem tensorPowerTarget_flat [Module.Flat k B] (q : ℕ) :
    Module.Flat k ((powerFunctor k q).obj (coefficientModule k B)) := by
  let _ : Module.Flat k (coefficientModule k B) := by change Module.Flat k B; infer_instance
  exact power_flat k (coefficientModule k B) q

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k` be flat over `k`, and `M : ModuleCat.{w} k` be
arbitrary. For every `q : ℕ`,
`QuasiIso (AlternatingFaceMapComplex.ε.app (arbitraryCoefficientTensorAugmented k B M q))`.
This map augments the alternating-face complex of `M ⊗_k P^{⊗ q}` to `M ⊗_k B^{⊗ q}` concentrated in degree zero. The
projective tensor-power resolution and its flat target justify tensoring with `M`. -/
theorem arbitraryCoefficientTensorAlternatingAugmentation_quasiIso [Module.Flat k B] (q : ℕ) :
    _root_.QuasiIso (AlternatingFaceMapComplex.ε.app (arbitraryCoefficientTensorAugmented k B M q)) := by
  let F := arbitraryCoefficientTensorFunctor k M
  let P := tensorPowerProjectiveResolution k B q
  let K : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    (F.mapHomologicalComplex (.down ℕ)).obj
      ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (tensorPowerDiagram k B q))
  let a : K ≅ (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
      (arbitraryCoefficientTensorDiagram k B M q) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app (tensorPowerDiagram k B q)
  let f : K ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj
      (F.obj ((powerFunctor k q).obj (coefficientModule k B))) :=
    ModuleCat.projectiveCoefficientAugmentation.{u, w, v} k M P
  let _ : Module.Flat k ((powerFunctor k q).obj (coefficientModule k B)) := tensorPowerTarget_flat k B q
  let _ : _root_.QuasiIso f := ModuleCat.projectiveCoefficientAugmentation_quasiIso_of_flat_target.{u, w, v} k M P
  have h : AlternatingFaceMapComplex.ε.app (arbitraryCoefficientTensorAugmented k B M q) = a.inv ≫ f := by
    apply (ChainComplex.toSingle₀Equiv
      ((alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (arbitraryCoefficientTensorDiagram k B M q))
      (F.obj ((powerFunctor k q).obj (coefficientModule k B)))).injective
    apply Subtype.ext
    change (AlternatingFaceMapComplex.ε.app (arbitraryCoefficientTensorAugmented k B M q)).f 0 = (a.inv ≫ f).f 0
    let X₀ := ((tensorPowerDiagram k B q).obj (op ⦋0⦌))
    let Y₀ := (powerFunctor k q).obj (coefficientModule k B)
    let α₀ : F.obj X₀ ⟶ F.obj Y₀ := F.map ((tensorPowerAugmentation k B q).app (op ⦋0⦌))
    have hε : (AlternatingFaceMapComplex.ε.app (arbitraryCoefficientTensorAugmented k B M q)).f 0 = α₀ :=
      (AlternatingFaceMapComplex.ε_app_f_zero (arbitraryCoefficientTensorAugmented k B M q)).trans
        (arbitraryCoefficientTensorAugmentation_app k B M q (op ⦋0⦌))
    have hf : f.f 0 = α₀ :=
      (ModuleCat.projectiveCoefficientAugmentation_f_zero.{u, w, v} k M P).trans
        (congrArg F.map (tensorPowerProjectiveResolution_π_f_zero k B q))
    have ha : a.inv.f 0 = 𝟙 (F.obj X₀) := rfl
    exact hε.trans ((HomologicalComplex.comp_f a.inv f 0).trans
      ((congrArg (fun t => t ≫ f.f 0) ha).trans
        ((Category.id_comp (f.f 0)).trans hf))).symm
  have hComp : _root_.QuasiIso (a.inv ≫ f) := _root_.quasiIso_comp a.inv f
  exact h.symm ▸ hComp

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
