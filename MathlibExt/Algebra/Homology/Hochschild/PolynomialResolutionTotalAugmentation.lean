/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionHorizontalAugmentation
public import MathlibExt.Algebra.Homology.BicomplexTotalAugmentation
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso

/-!
# Total augmentation from a polynomial resolution to Hochschild chains

For a commutative `k`-algebra `B`, the polynomial-resolution Hochschild bicomplex
has a horizontal augmentation in each Hochschild degree to the corresponding regular
Hochschild chain module placed in simplicial degree zero. These row augmentations
commute with the Hochschild boundary and assemble to a bicomplex map.

Totalization, with the total-degree flip isomorphism and its signs, gives a chain map
to the regular Hochschild complex. Its component on simplicial degree zero is the
coefficient-first polynomial augmentation; all positive simplicial-degree components
vanish. When `B` is flat over `k`, the total map is a quasi-isomorphism and induces
an isomorphism with Hochschild homology.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u v

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

local notation "C" => ModuleCat.{max u v} k
local notation "K" => bicomplex k B
local notation "L" => Symmetric.AugmentedAlgebra.regularComplex k B

/--
The chain-complex isomorphism between the horizontal row in Hochschild degree `q`
and the alternating-face complex of its simplicial module row diagram.
-/
def rowSourceIso (q : ℕ) : K.flip.X q ≅ (alternatingFaceMapComplex C).obj (rowDiagram k B q) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    (HomologicalComplex.eval C (.down ℕ) q)).app (diagram k B)

/--
The horizontal augmentation in Hochschild degree `q` to the regular Hochschild
module placed in simplicial chain degree zero.
-/
def horizontalAugmentationComponent (q : ℕ) : K.flip.X q ⟶
    (ChainComplex.single₀ C).obj (L.X q) :=
  (rowSourceIso k B q).hom ≫ AlternatingFaceMapComplex.ε.app (rowAugmented k B q)

/--
The simplicial-degree-zero component of the row augmentation is the degree-`q`
component of the polynomial diagram augmentation.
-/
theorem horizontalAugmentationComponent_f_zero (q : ℕ) :
    (horizontalAugmentationComponent k B q).f 0 = ((diagramAugmentation k B).app (Opposite.op ⦋0⦌)).f q := by
  rw [horizontalAugmentationComponent, HomologicalComplex.comp_f,
    AlternatingFaceMapComplex.ε_app_f_zero]
  change 𝟙 _ ≫ ((diagramAugmentation k B).app (Opposite.op ⦋0⦌)).f q = _
  exact Category.id_comp _

/--
Every positive simplicial-degree component of the horizontal augmentation in
Hochschild degree `q` is zero.
-/
theorem horizontalAugmentationComponent_f_succ (q p : ℕ) :
    (horizontalAugmentationComponent k B q).f (p + 1) = 0 := by
  rw [horizontalAugmentationComponent, HomologicalComplex.comp_f,
    AlternatingFaceMapComplex.ε_app_f_succ, CategoryTheory.Limits.comp_zero]

/--
The bicomplex map from the flipped polynomial-resolution Hochschild bicomplex to
its regular Hochschild complex placed in inner degree zero, assembled from the
horizontal row augmentations.
-/
def horizontalBicomplexAugmentation : K.flip ⟶ HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj L :=
  ChainComplex.ofHom (horizontalAugmentationComponent k B) (by
    intro q
    apply HomologicalComplex.to_single_hom_ext (j := 0)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      horizontalAugmentationComponent_f_zero, horizontalAugmentationComponent_f_zero]
    change ((diagramAugmentation k B).app (Opposite.op ⦋0⦌)).f (q + 1) ≫ L.d (q + 1) q =
      ((diagram k B).obj (Opposite.op ⦋0⦌)).d (q + 1) q ≫
        ((diagramAugmentation k B).app (Opposite.op ⦋0⦌)).f q
    exact ((diagramAugmentation k B).app (Opposite.op ⦋0⦌)).comm (q + 1) q)

/--
The chain map from the total polynomial-resolution Hochschild complex to the regular
Hochschild complex, obtained by the total-degree flip and totalization of the
horizontal augmentation. It uses the augmentation only in simplicial degree zero.
-/
def totalAugmentation : totalComplex k B ⟶ L :=
  (K.totalFlipIso (.down ℕ)).inv ≫
    HomologicalComplex₂.totalAugmentationDownNat (horizontalBicomplexAugmentation k B)

/--
The inclusion of bidegree `(0,q)` into total degree `q`, followed by the total
augmentation, is the degree-`q` polynomial Hochschild augmentation component.
-/
@[reassoc]
theorem totalAugmentation_zero_column (q : ℕ) :
    K.ιTotal (.down ℕ) 0 q q (Nat.zero_add q) ≫ (totalAugmentation k B).f q =
      ((diagramAugmentation k B).app (Opposite.op ⦋0⦌)).f q := by
  rw [totalAugmentation, HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
  simp only [HomologicalComplex.ComplexShape.σ_down_ℕ, Nat.zero_mul, pow_zero, one_smul]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_comp_totalAugmentationDownNat_zero,
    horizontalAugmentationComponent_f_zero]
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

section Flat

variable [Module.Flat k B]

/--
If `B` is flat over `k`, every horizontal augmentation in Hochschild degree `q`
is a quasi-isomorphism.
-/
theorem horizontalAugmentationComponent_quasiIso (q : ℕ) :
    QuasiIso (horizontalAugmentationComponent k B q) := by
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app (rowAugmented k B q)) :=
    rowAlternatingAugmentation_quasiIso k B q
  unfold horizontalAugmentationComponent
  infer_instance

/--
If `B` is flat over `k`, the total augmentation from the polynomial-resolution
Hochschild bicomplex to the regular Hochschild chain complex is a quasi-isomorphism.
-/
theorem totalAugmentation_quasiIso : QuasiIso (totalAugmentation k B) := by
  let f := horizontalBicomplexAugmentation k B
  have hf : ∀ q : ℕ, QuasiIso (f.f q) := horizontalAugmentationComponent_quasiIso k B
  letI : QuasiIso (HomologicalComplex₂.total.map f (.down ℕ)) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant f hf
  unfold totalAugmentation HomologicalComplex₂.totalAugmentationDownNat
  infer_instance

/--
Under flatness of `B` over `k`, the isomorphism from total homology in degree `n`
to regular Hochschild homology, induced by the total augmentation.
-/
def totalHochschildHomologyIso (n : ℕ) :
    (totalComplex k B).homology n ≅ (Symmetric.chainComplex k B B).homology n := by
  letI : QuasiIso (totalAugmentation k B) := totalAugmentation_quasiIso k B
  exact _root_.isoOfQuasiIsoAt (totalAugmentation k B) n

/--
The forward map of `totalHochschildHomologyIso` is precisely the homology map of
the total augmentation in the same degree `n`.
-/
theorem totalHochschildHomologyIso_hom (n : ℕ) :
    (totalHochschildHomologyIso k B n).hom = HomologicalComplex.homologyMap (totalAugmentation k B) n := rfl

end Flat

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
