/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.AugmentedHochschildCoefficients
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionCoefficientAugmentation
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.Algebra.Homology.BicomplexTotalAugmentation
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso

/-!
# Canonical Hochschild augmentation with arbitrary coefficients

Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `M : Type w` an
additive group with compatible `k`- and `B`-module actions (`SMulCommClass k B M` and
`IsScalarTower k B M`). The canonical polynomial resolution `P` gives a Hochschild bicomplex
with term `M ⊗_k P_p^{⊗ q}` at `(p,q)`. Its horizontal augmentation applies the algebra
augmentation to all tail factors and retains the coefficient.

The horizontal rows are coefficient tensors of polynomial tensor-power resolutions. If `B` is
flat over `k`, their augmentations are quasi-isomorphisms for arbitrary `M`. These row maps
assemble into a total augmentation to the Hochschild complex of `B` with coefficient `M`,
using the signed total-flip isomorphism. The total augmentation is then a quasi-isomorphism.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.AugmentedCoefficients.Canonical

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`, `resolution k B` is the
value of `polynomialResolutionOverFunctor k B` at the identity augmentation `B ⟶ B`. It is an
augmented simplicial polynomial resolution with augmentation object `B`. -/
abbrev resolution :=
  (CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B))

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `M : Type w` an
additive group with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B
M`. The simplicial chain diagram `diagram k B M` takes the level `P_p` of `resolution k B` to
its Hochschild complex with coefficient `M`, where `P_p` acts through its augmentation to `B`.
It takes values in `ChainComplex (ModuleCat.{max u v w} k) ℕ`. -/
def diagram : SimplicialObject (ChainComplex (ModuleCat.{max u v w} k) ℕ) :=
  AugmentedCoefficients.simplicialDiagram k B M (resolution k B)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive coefficient
`M : Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B
M`, `diagramAugmentation k B M` maps `diagram k B M` to the constant simplicial object with
value `terminalComplex k B M`. On a coefficient-first tensor, it retains `m ∈ M` and applies
the polynomial-resolution augmentation to each algebra tail factor. -/
def diagramAugmentation : diagram k B M ⟶
    (SimplicialObject.const (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj (terminalComplex k B M) :=
  AugmentedCoefficients.simplicialAugmentation k B M (resolution k B)

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `M : Type w` have an
additive group structure and actions satisfying `Module k M`, `Module B M`, `SMulCommClass k B
M`, and `IsScalarTower k B M`. Applying the alternating-face complex to `diagram k B M` gives
`bicomplex k B M`, with both shapes `.down ℕ` and values in `ModuleCat.{max u v w} k`. Its
term at `(p,q)` is `M ⊗_k P_p^{⊗ q}`. -/
def bicomplex : HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj (diagram k B M)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive coefficient
`M : Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B
M`, `rowDiagram k B M q` evaluates `diagram k B M` in Hochschild degree `q : ℕ`. It is the
simplicial `k`-module with terms `M ⊗_k P_p^{⊗ q}` in the polynomial-resolution direction. -/
def rowDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v w} k) :=
  diagram k B M ⋙ HomologicalComplex.eval (ModuleCat.{max u v w} k) (.down ℕ) q

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `M : Type w` an additive coefficient with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`. For `q : ℕ`, evaluation and the
alternating-face construction give an isomorphism
`(bicomplex k B M).flip.X q ≅ (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (rowDiagram k B M q)`. -/
def rowSourceIso (q : ℕ) : (bicomplex k B M).flip.X q ≅
    (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (rowDiagram k B M q) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    (HomologicalComplex.eval (ModuleCat.{max u v w} k) (.down ℕ) q)).app (diagram k B M)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive coefficient `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`, there is a simplicial-module isomorphism
`rowDiagram k B M q ≅ AndreQuillenResolution.arbitraryCoefficientTensorDiagram k B (ModuleCat.of k M) q`
for every `q : ℕ`. Both sides have terms `M ⊗_k P_p^{⊗ q}`, with the same coefficient-first tensor order. -/
def rowTensorIso (q : ℕ) : rowDiagram k B M q ≅
    AndreQuillenResolution.arbitraryCoefficientTensorDiagram k B (ModuleCat.of k M) q :=
  NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j θ
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change (((diagram k B M).map θ).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.map
        (fun _ : Fin q => ((AndreQuillenResolution.additiveDiagram k B).map θ).hom)
          (PiTensorProduct.tprod k a)
    have h := AugmentedCoefficients.simplicialDiagram_map_tprod k B M (resolution k B) θ q m a
    have ht := PiTensorProduct.map_tprod
      (fun _ : Fin q => ((AndreQuillenResolution.additiveDiagram k B).map θ).hom) a
    exact h.trans (congrArg
      (fun z : TensorPower k q ((AndreQuillenResolution.additiveDiagram k B).obj j) =>
        m ⊗ₜ[k] z) ht).symm)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`, the coefficient tensor target is identified with
degree `q : ℕ` of the terminal Hochschild complex:
`(AndreQuillenResolution.arbitraryCoefficientTensorFunctor k (ModuleCat.of k M)).obj (B^{⊗ q}) ≅ (terminalComplex k B
M).X q`.
Both modules represent `M ⊗_k B^{⊗ q}` in universe `max u v w`. -/
def rowTargetIso (q : ℕ) :
    ((AndreQuillenResolution.arbitraryCoefficientTensorFunctor k (ModuleCat.of k M)).obj
      ((CategoryTheory.SimplicialObject.ModuleTensor.powerFunctor k q).obj
        (AndreQuillenResolution.coefficientModule k B))) ≅ (terminalComplex k B M).X q := Iso.refl _

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, an additive `k`-module `M :
Type w`, and `q : ℕ`, `tensorRowComplex k B M q` is the alternating-face complex of
`(AndreQuillenResolution.arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M) q).left`.
Its degree-`p` term represents `M ⊗_k P_p^{⊗ q}` in `ModuleCat.{max u v w} k`. -/
abbrev tensorRowComplex (q : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
    (AndreQuillenResolution.arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M) q).left

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, an additive `k`-module `M :
Type w`, and `q : ℕ`, `tensorRowSingle k B M q` is the chain complex concentrated in degree
zero at the augmentation object of `arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M)
q`. That object represents `M ⊗_k B^{⊗ q}`. -/
abbrev tensorRowSingle (q : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj
    (AndreQuillenResolution.arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M) q).right

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`. For every `q : ℕ`,
`(bicomplex k B M).flip.X q ≅ tensorRowComplex k B M q`.
The isomorphism composes the alternating-face/evaluation comparison with the row's coefficient-tensor identification. -/
def horizontalRowIso (q : ℕ) : (bicomplex k B M).flip.X q ≅ tensorRowComplex k B M q :=
  rowSourceIso k B M q ≪≫
    (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).mapIso (rowTensorIso k B M q)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, an additive `k`-module `M : Type w`, and `q : ℕ`,
the map
`tensorRowComplex k B M q ⟶ tensorRowSingle k B M q`
is `AlternatingFaceMapComplex.ε.app (AndreQuillenResolution.arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M)
q)`. It augments the alternating tensor row to `M ⊗_k B^{⊗ q}` in degree zero. -/
def tensorRowAugmentation (q : ℕ) : tensorRowComplex k B M q ⟶ tensorRowSingle k B M q :=
  AlternatingFaceMapComplex.ε.app
    (AndreQuillenResolution.arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M) q)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`, there is an isomorphism
`tensorRowSingle k B M q ≅ (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj ((terminalComplex k B M).X q)`
for `q : ℕ`. It is the single-degree image of the coefficient-target isomorphism `rowTargetIso k B M q`. -/
def horizontalTargetIso (q : ℕ) : tensorRowSingle k B M q ≅
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj ((terminalComplex k B M).X q) :=
  (ChainComplex.single₀ (ModuleCat.{max u v w} k)).mapIso (rowTargetIso k B M q)

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`. For `q : ℕ`, the row map to the terminal
Hochschild degree concentrated at zero is
`(horizontalRowIso k B M q).hom ≫ tensorRowAugmentation k B M q ≫ (horizontalTargetIso k B M q).hom`.
Its source is `(bicomplex k B M).flip.X q` and its target is `single₀ ((terminalComplex k B M).X q)`. -/
def horizontalAugmentationComponent (q : ℕ) : (bicomplex k B M).flip.X q ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj ((terminalComplex k B M).X q) :=
  (horizontalRowIso k B M q).hom ≫ tensorRowAugmentation k B M q ≫ (horizontalTargetIso k B M q).hom

omit [Algebra ℚ k] in
/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`, every `q : ℕ` satisfies
`(horizontalAugmentationComponent k B M q).f 0 = ((diagramAugmentation k B M).app (op ⦋0⦌)).f q`.
The horizontal map's degree-zero component is exactly the Hochschild augmentation in degree `q` at polynomial-resolution
level zero. -/
theorem horizontalAugmentationComponent_f_zero (q : ℕ) :
    (horizontalAugmentationComponent k B M q).f 0 =
      ((diagramAugmentation k B M).app (op ⦋0⦌)).f q := by
  let a := horizontalRowIso k B M q
  let b := tensorRowAugmentation k B M q
  let c := horizontalTargetIso k B M q
  let α : ((rowDiagram k B M q).obj (op ⦋0⦌)) ⟶ (terminalComplex k B M).X q :=
    (AndreQuillenResolution.arbitraryCoefficientTensorAugmentation k B (ModuleCat.of k M) q).app (op ⦋0⦌)
  have ha : a.hom.f 0 = 𝟙 ((rowDiagram k B M q).obj (op ⦋0⦌)) := rfl
  have hb : b.f 0 = α :=
    AlternatingFaceMapComplex.ε_app_f_zero
      (AndreQuillenResolution.arbitraryCoefficientTensorAugmented k B (ModuleCat.of k M) q)
  have hc : c.hom.f 0 = 𝟙 ((terminalComplex k B M).X q) := rfl
  have hα : α = ((diagramAugmentation k B M).app (op ⦋0⦌)).f q := by
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m t
    have ht := AugmentedCoefficients.simplicialAugmentation_tprod k B M (resolution k B)
      (op ⦋0⦌) q m t
    have hs := AndreQuillenResolution.tensorPowerAugmentation_tprod k B q (op ⦋0⦌) t
    change m ⊗ₜ[k] ((AndreQuillenResolution.tensorPowerAugmentation k B q).app (op ⦋0⦌)).hom
        (PiTensorProduct.tprod k t) = (((diagramAugmentation k B M).app (op ⦋0⦌)).f q).hom
          (m ⊗ₜ[k] PiTensorProduct.tprod k t)
    exact (congrArg (fun z => m ⊗ₜ[k] z) hs).trans ht.symm
  change (a.hom ≫ b ≫ c.hom).f 0 = _
  exact (HomologicalComplex.comp_f a.hom (b ≫ c.hom) 0).trans
    ((congrArg₂ (fun x y => x ≫ y) ha (HomologicalComplex.comp_f b c.hom 0)).trans
      ((congrArg (fun t => 𝟙 _ ≫ t) (congrArg₂ (fun x y => x ≫ y) hb hc)).trans
        ((Category.id_comp _).trans ((Category.comp_id _).trans hα))))

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`. The morphism
`(bicomplex k B M).flip ⟶ HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj (terminalComplex k B M)`
has component `horizontalAugmentationComponent k B M q` in each degree `q`. The Hochschild chain-map equation of the
diagram augmentation gives compatibility between consecutive rows. -/
def horizontalBicomplexAugmentation : (bicomplex k B M).flip ⟶
    HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj (terminalComplex k B M) :=
  ChainComplex.ofHom (horizontalAugmentationComponent k B M) (by
    intro q
    apply HomologicalComplex.to_single_hom_ext (j := 0)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      horizontalAugmentationComponent_f_zero, horizontalAugmentationComponent_f_zero]
    change ((diagramAugmentation k B M).app (op ⦋0⦌)).f (q + 1) ≫
        (terminalComplex k B M).d (q + 1) q =
      ((diagram k B M).obj (op ⦋0⦌)).d (q + 1) q ≫
        ((diagramAugmentation k B M).app (op ⦋0⦌)).f q
    exact ((diagramAugmentation k B M).app (op ⦋0⦌)).comm (q + 1) q)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`,
`totalComplex k B M` is `(bicomplex k B M).total (.down ℕ)`. Its degree-`n` term is the direct
sum of `M ⊗_k P_p^{⊗ q}` over `p+q=n`, with the down-`ℕ` totalization signs and carrier
universe `max u v w`. -/
abbrev totalComplex := (bicomplex k B M).total (.down ℕ)

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`. The map `totalComplex k B M ⟶
terminalComplex k B M` is
`((bicomplex k B M).totalFlipIso (.down ℕ)).inv ≫ HomologicalComplex₂.totalAugmentationDownNat
(horizontalBicomplexAugmentation k B M)`.
It uses the inverse signed total-flip isomorphism followed by the assembled horizontal augmentation. -/
def totalAugmentation : totalComplex k B M ⟶ terminalComplex k B M :=
  ((bicomplex k B M).totalFlipIso (.down ℕ)).inv ≫
    HomologicalComplex₂.totalAugmentationDownNat (horizontalBicomplexAugmentation k B M)

omit [Algebra ℚ k] in
/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k` be flat over `k`, and let
`M : Type w` be an additive group with `Module k M`, `Module B M`, `SMulCommClass k B M`, and
`IsScalarTower k B M`. For every `q : ℕ`, `horizontalAugmentationComponent k B M q` is a
quasi-isomorphism. It compares the alternating polynomial tensor row with `M ⊗_k B^{⊗ q}`
concentrated at degree zero, using the projective tensor-power resolution and its flat target. -/
theorem horizontalAugmentationComponent_quasiIso [Module.Flat k B] (q : ℕ) :
    _root_.QuasiIso (horizontalAugmentationComponent k B M q) := by
  let b := tensorRowAugmentation k B M q
  let _ : _root_.QuasiIso b :=
    AndreQuillenResolution.arbitraryCoefficientTensorAlternatingAugmentation_quasiIso k B (ModuleCat.of k M) q
  let _ : _root_.QuasiIso (b ≫ (horizontalTargetIso k B M q).hom) :=
    _root_.quasiIso_comp b (horizontalTargetIso k B M q).hom
  exact _root_.quasiIso_comp (horizontalRowIso k B M q).hom
    (b ≫ (horizontalTargetIso k B M q).hom)

/-- For a commutative ring `k : Type u`, a `k`-flat algebra `B : CommAlgCat.{max u v} k`, and an
additive group `M : Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and
`IsScalarTower k B M`, the map `totalAugmentation k B M : totalComplex k B M ⟶ terminalComplex
k B M` is a quasi-isomorphism. Thus the signed total of the canonical polynomial-resolution
Hochschild bicomplex computes the Hochschild homology of `B` with coefficient `M`. -/
instance totalAugmentation_quasiIso [Module.Flat k B] : _root_.QuasiIso (totalAugmentation k B M) := by
  let f := horizontalBicomplexAugmentation k B M
  have hf : ∀ q : ℕ, _root_.QuasiIso (f.f q) := horizontalAugmentationComponent_quasiIso k B M
  let _ : _root_.QuasiIso (HomologicalComplex₂.total.map f (.down ℕ)) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant f hf
  unfold totalAugmentation HomologicalComplex₂.totalAugmentationDownNat
  infer_instance

end ModuleCat.Algebra.Hochschild.Symmetric.AugmentedCoefficients.Canonical
