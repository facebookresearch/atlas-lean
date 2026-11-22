/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CoproductIntegerSplitting
import MathlibExt.AlgebraicTopology.ModelCategory.CoproductWeakEquivalences
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.FiniteProducts
import MathlibExt.CategoryTheory.Limits.FiniteCoproductCoordinates

/-!
# Actual integer stable-pi groups of finite original coproducts

The exact original binary split is iterated over the actual chosen
finite coproducts. The successor Iso retains the same original labels
and injections. All coordinate maps remain the original zero/identity
maps on those summands.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.FiniteCoproductIntegerPiGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  Diagrams.nativeHasZeroObject HasZeroObject.zeroMorphismsOfZeroObject

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}

/-- The original coordinate map is identity on its own original summand and zero on every other summand. -/
abbrev coordinate {n : ℕ} (X : Fin n → Carrier.{u, v}) (i : Fin n) : (∐ X) ⟶ X i :=
  CategoryTheory.Limits.FiniteCoproductCoordinates.coordinate X i

omit B in
private theorem null_eq_zero (X Y : Carrier.{u, v}) : Diagrams.toZero X ≫ Diagrams.zeroTo Y = (0 : X ⟶ Y) :=
  (congrArg (fun f => Diagrams.toZero X ≫ f)
    (Diagrams.zeroDiagram_isZero.eq_zero_of_src (Diagrams.zeroTo Y))).trans comp_zero

private def emptyIso (X : Fin 0 → Carrier.{u, v}) : (∐ X) ≅ Diagrams.zeroDiagram :=
  (IsInitial.ofUniqueHom (fun Y => Sigma.desc (fun i => Fin.elim0 i)) (by
    intro Y f
    apply Sigma.hom_ext
    intro i
    exact Fin.elim0 i)).uniqueUpToIso Diagrams.zeroDiagramIsInitial

/-- The actual finite coproduct group is the full coordinate family of the original integer groups. -/
def equiv (q : ℤ) (n : ℕ) (X : Fin n → Carrier.{u, v}) (hX : ∀ i, IsCofibrant (X i)) :
    (integerStablePiFunctor q).obj (∐ X) ≃* ∀ i, (integerStablePiFunctor q).obj (X i) := by
  induction n with
  | zero =>
    let _ : Subsingleton ((integerStablePiFunctor q).obj Diagrams.zeroDiagram) := integerZero_subsingleton q
    let e := (integerStablePiFunctor q).mapIso (emptyIso X)
    let _ : Subsingleton ((integerStablePiFunctor q).obj (∐ X)) :=
      e.groupIsoToMulEquiv.injective.subsingleton
    let _ : Unique ((integerStablePiFunctor q).obj (∐ X)) := uniqueOfSubsingleton 1
    let _ : Unique (∀ i, (integerStablePiFunctor q).obj (X i)) := uniqueOfSubsingleton (fun i => Fin.elim0 i)
    exact MulEquiv.ofUnique
  | succ n ih =>
    let Y := CategoryTheory.Limits.FiniteCoproductSuccessor.tail X
    let _ : IsCofibrant (X 0) := hX 0
    let _ : IsCofibrant (∐ Y) :=
      @originalCofanPoint_cofibrant Carrier.{u, v} inferInstance
        (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory.{u, v} (B := B))
        (Fin n) Y (Cofan.mk (∐ Y) (Sigma.ι Y)) (coproductIsCoproduct Y)
        (fun i => hX i.succ)
    let e₁ := (integerStablePiFunctor q).mapIso (CategoryTheory.Limits.FiniteCoproductSuccessor.iso X)
    let e₂ := CoproductIntegerSplittingGeometry.equiv (B := B) (X 0) (∐ Y) q
    let e₃ := MulEquiv.prodCongr (MulEquiv.refl ((integerStablePiFunctor q).obj (X 0)))
      (ih Y (fun i => hX i.succ))
    let e₄ : ((integerStablePiFunctor q).obj (X 0) × ∀ i, (integerStablePiFunctor q).obj (Y i)) ≃*
        ∀ i : Fin (n + 1), (integerStablePiFunctor q).obj (X i) := {
      toEquiv := Fin.consEquiv (fun i => (integerStablePiFunctor q).obj (X i))
      map_mul' := by intro a b; funext i; refine Fin.cases rfl (fun j => rfl) i }
    exact e₁.groupIsoToMulEquiv.trans (e₂.trans (e₃.trans e₄))

/-- The entire original finite coproduct equivalence reads every original integer coordinate map. -/
theorem equiv_coordinate (q : ℤ) (n : ℕ) (X : Fin n → Carrier.{u, v})
    (hX : ∀ i, IsCofibrant (X i)) (z : (integerStablePiFunctor q).obj (∐ X)) (i : Fin n) :
    equiv (B := B) q n X hX z i = ((integerStablePiFunctor q).map (coordinate X i)).hom z := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let Y := CategoryTheory.Limits.FiniteCoproductSuccessor.tail X
    let _ : IsCofibrant (X 0) := hX 0
    let _ : IsCofibrant (∐ Y) :=
      @originalCofanPoint_cofibrant Carrier.{u, v} inferInstance
        (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory.{u, v} (B := B))
        (Fin n) Y (Cofan.mk (∐ Y) (Sigma.ι Y)) (coproductIsCoproduct Y)
        (fun i => hX i.succ)
    let e := CategoryTheory.Limits.FiniteCoproductSuccessor.iso X
    let a := ((integerStablePiFunctor q).map e.hom).hom z
    refine Fin.cases ?_ (fun j => ?_) i
    · have hc : e.hom ≫ CoproductIntegerSplittingGeometry.leftProjection (X 0) (∐ Y) = coordinate X 0 := by
        have hn := null_eq_zero (∐ Y) (X 0)
        exact (congrArg (fun f => e.hom ≫ coprod.desc (𝟙 (X 0)) f) hn).trans
          (CategoryTheory.Limits.FiniteCoproductCoordinates.first X)
      have hm := ConcreteCategory.congr_hom
        ((integerStablePiFunctor q).map_comp e.hom
          (CoproductIntegerSplittingGeometry.leftProjection (X 0) (∐ Y))) z
      exact hm.symm.trans (ConcreteCategory.congr_hom ((integerStablePiFunctor q).congr_map hc) z)
    · have hc : e.hom ≫ CoproductIntegerPiGeometry.rightProjection (X 0) (∐ Y) ≫ coordinate Y j =
          coordinate X j.succ := by
        have hn := null_eq_zero (X 0) (∐ Y)
        exact (congrArg (fun f => e.hom ≫ coprod.desc f (𝟙 (∐ Y)) ≫ coordinate Y j) hn).trans
          (CategoryTheory.Limits.FiniteCoproductCoordinates.successor X j)
      have htail := ih Y (fun i => hX i.succ)
        (((integerStablePiFunctor q).map (CoproductIntegerPiGeometry.rightProjection (X 0) (∐ Y))).hom a) j
      have hm := ConcreteCategory.congr_hom
        ((integerStablePiFunctor q).map_comp e.hom
          (CoproductIntegerPiGeometry.rightProjection (X 0) (∐ Y) ≫ coordinate Y j)) z
      have hn := ConcreteCategory.congr_hom
        ((integerStablePiFunctor q).map_comp (CoproductIntegerPiGeometry.rightProjection (X 0) (∐ Y))
          (coordinate Y j)) a
      exact htail.trans (hn.symm.trans (hm.symm.trans
        (ConcreteCategory.congr_hom ((integerStablePiFunctor q).congr_map hc) z)))

end PointedCGWH.SequentialSpectrum.StableHomotopy.FiniteCoproductIntegerPiGeometry
