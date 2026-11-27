/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionTensorPowers
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionDiagram

/-!
# Horizontal augmentation of the polynomial Hochschild resolution

Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `P` its canonical
simplicial polynomial resolution. In fixed Hochschild degree `q`, the horizontal row has terms
`B ⊗_k P_i^{⊗ q}`. Its augmentation to the constant module `B ⊗_k B^{⊗ q}` applies the
resolution augmentation to every tail factor and retains the first coefficient.

If `B` is flat over `k`, the map on alternating-face complexes is a quasi-isomorphism. The
augmented row also has a quasi-isomorphism from its alternating-face complex to the regular
Hochschild degree-`q` module concentrated in chain degree zero.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology Opposite
open scoped TensorProduct Simplicial

universe u v

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, `rowDiagram k
B q` is the simplicial `k`-module obtained by evaluating the polynomial-resolution Hochschild
chain diagram in degree `q`. At simplicial degree `i`, its term is `B ⊗_k P_i^{⊗ q}`, where `P
= resolution k B`. -/
abbrev rowDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v} k) :=
  diagram.{u, v} k B ⋙ HomologicalComplex.eval (ModuleCat.{max u v} k) (.down ℕ) q

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `q : ℕ`. The
simplicial map `rowAugmentation k B q` goes from `rowDiagram k B q` to the constant simplicial
module with value `(Symmetric.AugmentedAlgebra.regularComplex k B).X q`. It is obtained by
evaluating the Hochschild diagram augmentation in degree `q`. -/
def rowAugmentation (q : ℕ) : rowDiagram.{u, v} k B q ⟶
    (SimplicialObject.const (ModuleCat.{max u v} k)).obj
      ((Symmetric.AugmentedAlgebra.regularComplex.{u, v} k B).X q) :=
  Functor.whiskerRight (diagramAugmentation.{u, v} k B)
      (HomologicalComplex.eval (ModuleCat.{max u v} k) (.down ℕ) q) ≫
    (Functor.constComp SimplexCategoryᵒᵖ (Symmetric.AugmentedAlgebra.regularComplex.{u, v} k B)
      (HomologicalComplex.eval (ModuleCat.{max u v} k) (.down ℕ) q)).hom

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, there is an isomorphism of
simplicial `k`-modules
`rowDiagram k B q ≅ coefficientTensorDiagram k B q`.
Both diagrams have terms `B ⊗_k P_i^{⊗ q}` for `P = resolution k B`, with simplicial operators acting on each tail
factor. -/
def rowTensorIso (q : ℕ) : rowDiagram.{u, v} k B q ≅ coefficientTensorDiagram.{u, v} k B q :=
  NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j θ
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro b a
    change (((diagram.{u, v} k B).map θ).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      b ⊗ₜ[k] PiTensorProduct.map
        (fun _ : Fin q => ((additiveDiagram.{u, v} k B).map θ).hom) (PiTensorProduct.tprod k a)
    have h := diagram_map_tprod.{u, v} k B θ q b a
    have hTail := PiTensorProduct.map_tprod
      (fun _ : Fin q => ((additiveDiagram.{u, v} k B).map θ).hom) a
    exact h.trans (congrArg (fun t => b ⊗ₜ[k] t) hTail.symm))

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, the coefficient tensor target `B ⊗_k
B^{⊗ q}` is identified with degree `q` of the regular Hochschild chain complex:
`coefficientTarget k B q ≅ (Symmetric.AugmentedAlgebra.regularComplex k B).X q`. -/
def coefficientTargetIso (q : ℕ) : coefficientTarget.{u, v} k B q ≅
    (Symmetric.AugmentedAlgebra.regularComplex.{u, v} k B).X q := by
  rw [Symmetric.AugmentedAlgebra.regularComplex_eq.{u, v}]
  rfl

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, `q : ℕ`, and `i : SimplexCategoryᵒᵖ`. For `b :
coefficientModule k B` and `a : Fin q → (additiveDiagram k B).obj i`,
`((coefficientTensorAugmentation k B q).app i).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) = b ⊗ₜ[k] PiTensorProduct.tprod k
(fun j => ((additiveAugmentation k B).app i).hom (a j))`.
The coefficient `b` is retained and every tail entry is augmented. -/
theorem coefficientTensorAugmentation_tprod (q : ℕ) (i : SimplexCategoryᵒᵖ)
    (b : coefficientModule.{u, v} k B) (a : Fin q → (additiveDiagram.{u, v} k B).obj i) :
    ((coefficientTensorAugmentation.{u, v} k B q).app i).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      b ⊗ₜ[k] PiTensorProduct.tprod k
        (fun j => ((additiveAugmentation.{u, v} k B).app i).hom (a j)) := by
  change b ⊗ₜ[k]
    (((tensorPowerAugmentation.{u, v} k B q).app i).hom (PiTensorProduct.tprod k a)) = _
  exact congrArg (fun t => b ⊗ₜ[k] t) (tensorPowerAugmentation_tprod.{u, v} k B q i a)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`,
`rowAugmentation k B q = (rowTensorIso k B q).hom ≫ coefficientTensorAugmentation k B q ≫ (SimplicialObject.const
(ModuleCat.{max u v} k)).map (coefficientTargetIso k B q).hom`.
Thus the row augmentation is the coefficient-tensor augmentation expressed through the row and target identifications.
-/
theorem rowAugmentation_eq (q : ℕ) :
    rowAugmentation.{u, v} k B q =
      (rowTensorIso.{u, v} k B q).hom ≫ coefficientTensorAugmentation.{u, v} k B q ≫
        (SimplicialObject.const (ModuleCat.{max u v} k)).map (coefficientTargetIso.{u, v} k B q).hom := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro b a
  change (((diagramAugmentation.{u, v} k B).app i).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
    ((coefficientTensorAugmentation.{u, v} k B q).app i).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a)
  have h := Symmetric.AugmentedAlgebra.simplicialAugmentation_tprod.{u, v}
    k B (resolution.{u, v} k B) i q b a
  exact h.trans (coefficientTensorAugmentation_tprod.{u, v} k B q i b a).symm

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be flat as a
`k`-module. For every `q : ℕ`, applying `alternatingFaceMapComplex (ModuleCat.{max u v} k)` to
`rowAugmentation k B q` gives a quasi-isomorphism from the alternating-face complex of the
horizontal row to that of the constant regular Hochschild degree-`q` module. -/
theorem rowAugmentation_quasiIso [Module.Flat k B] (q : ℕ) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map
      (rowAugmentation.{u, v} k B q)) := by
  let A := alternatingFaceMapComplex (ModuleCat.{max u v} k)
  let α := (rowTensorIso.{u, v} k B q).hom
  let β := coefficientTensorAugmentation.{u, v} k B q
  let γ := (SimplicialObject.const (ModuleCat.{max u v} k)).map
    (coefficientTargetIso.{u, v} k B q).hom
  letI : IsIso α := inferInstance
  letI : IsIso γ := inferInstance
  letI : QuasiIso (A.map β) := coefficientTensorAugmentation_quasiIso.{u, v} k B q
  have hComp : QuasiIso (A.map α ≫ A.map β ≫ A.map γ) := inferInstance
  have hMap : A.map (α ≫ β ≫ γ) = A.map α ≫ A.map β ≫ A.map γ :=
    (A.map_comp α (β ≫ γ)).trans
      (congrArg (fun f => A.map α ≫ f) (A.map_comp β γ))
  have h : A.map (rowAugmentation.{u, v} k B q) = A.map α ≫ A.map β ≫ A.map γ :=
    (congrArg A.map (rowAugmentation_eq.{u, v} k B q)).trans hMap
  exact h.symm ▸ hComp

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, the augmented
simplicial `k`-module `rowAugmented k B q` has simplicial part `rowDiagram k B q`,
augmentation object `(Symmetric.AugmentedAlgebra.regularComplex k B).X q`, and augmentation
map `rowAugmentation k B q`. -/
def rowAugmented (q : ℕ) : SimplicialObject.Augmented (ModuleCat.{max u v} k) where
  left := rowDiagram.{u, v} k B q
  right := (Symmetric.AugmentedAlgebra.regularComplex.{u, v} k B).X q
  hom := rowAugmentation.{u, v} k B q

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k` be flat over `k`. For every `q : ℕ`,
`QuasiIso (AlternatingFaceMapComplex.ε.app (rowAugmented k B q))`.
This augmentation goes from the alternating-face complex of the horizontal polynomial-resolution row to the regular
Hochschild degree-`q` module concentrated in chain degree zero. -/
theorem rowAlternatingAugmentation_quasiIso [Module.Flat k B] (q : ℕ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (rowAugmented.{u, v} k B q)) := by
  let X := rowAugmented.{u, v} k B q
  let Y := (SimplicialObject.Augmented.const (C := ModuleCat.{max u v} k)).obj X.right
  let A := alternatingFaceMapComplex (ModuleCat.{max u v} k)
  let φ := A.map X.hom
  let ψ := AlternatingFaceMapComplex.ε.app Y
  let χ := AlternatingFaceMapComplex.ε.app X
  letI : QuasiIso φ := rowAugmentation_quasiIso.{u, v} k B q
  letI : QuasiIso ψ :=
    (SimplicialObject.Augmented.constantRightExtraDegeneracy X.right).quasiIso_augmentation
  have h := AlternatingFaceMapComplex.ε.naturality
    (SimplicialObject.Augmented.augmentationToConstant X)
  change φ ≫ ψ = χ ≫ (ChainComplex.single₀ (ModuleCat.{max u v} k)).map (𝟙 X.right) at h
  have hId := (ChainComplex.single₀ (ModuleCat.{max u v} k)).map_id X.right
  have hAug : φ ≫ ψ = χ :=
    h.trans ((congrArg (fun f => χ ≫ f) hId).trans (Category.comp_id χ))
  have hComp : QuasiIso (φ ≫ ψ) :=
    quasiIso_comp φ ψ
      (hφ := rowAugmentation_quasiIso.{u, v} k B q)
      (hφ' := (SimplicialObject.Augmented.constantRightExtraDegeneracy X.right).quasiIso_augmentation)
  change QuasiIso χ
  exact Eq.mp
    (congrArg
      (fun f : A.obj X.left ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} k)).obj X.right =>
        QuasiIso f) hAug) hComp

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
