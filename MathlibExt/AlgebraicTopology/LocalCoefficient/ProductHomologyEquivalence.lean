/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProductIdentityFiber
public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalence
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularHomology

/-!
# Products of actual integer-local-coefficient homology equivalences

For a product with an identity, its original ending fiber projects by a
derived trivial fibration to the old ending fiber. The same integral
terminal-map isomorphisms transfer through that actual projection. The
existing one-fiber coefficient criterion supplies every original target
integer system, including nonflat stalks. Products of two maps then follow
by the original coefficient composition and braiding formulas. No tensor
flatness, Kunneth comparison, or product-acyclicity witness is assumed.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

private theorem pathConnected_categoricalProduct (A B : TopCat.{u})
    [PathConnectedSpace A] [PathConnectedSpace B] : PathConnectedSpace ↑(A ⨯ B) :=
  (TopCat.homeoOfIso (TopCat.prodIsoProd A B)).symm.pathConnectedSpace

/-- The original terminal maps of a product-with-identity ending fiber are
invertible, by its actual weak projection and the original all-system map. -/
public theorem homotopyFiber_prodIdentity_terminalHomology_isIso
    {X A : TopCat.{u}} (f : X ⟶ A)
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (Y : TopCat.{u}) (z : ↑(A ⨯ Y)) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (homotopyFiber (prod.map f (𝟙 Y)) z))) := by
  let FP := homotopyFiber (prod.map f (𝟙 Y)) z
  let FI := homotopyFiber f ((prod.fst : A ⨯ Y ⟶ A) z)
  let q : FP ⟶ FI := homotopyFiberProdIdentityProjection f Y z
  let H := AlgebraicTopology.singularIntegralHomologyFunctor.{u} n
  have hq : TopCat.weakHomotopyEquivalences q :=
    homotopyFiberProdIdentityProjection_mem_weakHomotopyEquivalences f Y z
  let : IsIso (H.map q) :=
    hq.isIso_singularHomologyFunctor_map AlgebraicTopology.singularIntegralCoefficients.{u} n
  let : IsIso (H.map (terminal.from FI)) :=
    homotopyFiber_terminalHomology_isIso_of_localCoefficientHomologyEquivalence
      f hf ((prod.fst : A ⨯ Y ⟶ A) z) n
  have ht : terminal.from FP = q ≫ terminal.from FI := terminalIsTerminal.hom_ext _ _
  change IsIso (H.map (terminal.from FP))
  rw [ht, Functor.map_comp]
  infer_instance

namespace IsLocalCoefficientHomologyEquivalence

/-- The actual product with an identity preserves EVERY integer local
system. Path-connectedness is required only for its target factors. -/
public theorem prodWithIdentity
    {X A : TopCat.{u}} {f : X ⟶ A} [PathConnectedSpace A]
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (Y : TopCat.{u}) [PathConnectedSpace Y] :
    TopCat.IsLocalCoefficientHomologyEquivalence (prod.map f (𝟙 Y)) := by
  let : PathConnectedSpace ↑(A ⨯ Y) := pathConnected_categoricalProduct A Y
  let a : A := Classical.choice (inferInstance : Nonempty A)
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  let z : ↑(A ⨯ Y) := (TopCat.prodIsoProd A Y).inv (a, y)
  intro L n
  let m := TopCat.localCoefficientPullbackChainMap (prod.map f (𝟙 Y)) L
  let : QuasiIso m :=
    localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber
      (prod.map f (𝟙 Y)) z
      (fun k => homotopyFiber_prodIdentity_terminalHomology_isIso f hf Y z k) L
  change IsIso (HomologicalComplex.homologyMap m n)
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap m n).mp inferInstance

private theorem braiding_allLocalCoefficients (A B : TopCat.{u}) :
    TopCat.IsLocalCoefficientHomologyEquivalence (prod.braiding A B).hom :=
  TopCat.IsLocalCoefficientHomologyEquivalence.of_isIso (prod.braiding A B).hom

/-- The first-identity product is the same derived result through the
actual two braiding Isos; no new comparison or fiber witness is supplied. -/
public theorem identityProd
    {Y B : TopCat.{u}} {g : Y ⟶ B} [PathConnectedSpace B]
    (hg : TopCat.IsLocalCoefficientHomologyEquivalence g)
    (A : TopCat.{u}) [PathConnectedSpace A] :
    TopCat.IsLocalCoefficientHomologyEquivalence (prod.map (𝟙 A) g) := by
  have hs := braiding_allLocalCoefficients A Y
  have hm := hg.prodWithIdentity A
  have ht := braiding_allLocalCoefficients B A
  have he : prod.map (𝟙 A) g = (prod.braiding A Y).hom ≫
      prod.map g (𝟙 A) ≫ (prod.braiding B A).hom := by
    have h := congrArg (fun k => k ≫ (prod.braiding B A).hom)
        (CategoryTheory.Limits.braid_natural (𝟙 A) g)
    simpa only [Category.assoc, prod.symmetry, Category.comp_id] using h
  rw [he]
  exact hs.comp (hm.comp ht)

/-- Products preserve the original all-integer-local-system comparison on
path-connected targets. The first target and the second source are also
path connected, as they are for the canonical BGL-plus construction. -/
public theorem prodMap
    {X Y A B : TopCat.{u}} {f : X ⟶ A} {g : Y ⟶ B}
    [PathConnectedSpace Y] [PathConnectedSpace A] [PathConnectedSpace B]
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hg : TopCat.IsLocalCoefficientHomologyEquivalence g) :
    TopCat.IsLocalCoefficientHomologyEquivalence (prod.map f g) := by
  have h₁ := hf.prodWithIdentity Y
  have h₂ := hg.identityProd A
  have he : prod.map f (𝟙 Y) ≫ prod.map (𝟙 A) g = prod.map f g := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, Category.comp_id]
    · simp only [Category.assoc, prod.map_snd]
      simpa only [Category.id_comp] using (prod.map_snd_assoc f (𝟙 Y) g)
  exact he ▸ h₁.comp h₂

private theorem iso_allLocalCoefficients {A B : TopCat.{u}} (e : A ≅ B) :
    TopCat.IsLocalCoefficientHomologyEquivalence e.hom :=
  TopCat.IsLocalCoefficientHomologyEquivalence.of_isIso e.hom

/-- The same product theorem for the literal product of the underlying
spaces and the literal pair of the two original continuous maps. -/
public theorem prodContinuousMap
    {X Y A B : TopCat.{u}} {f : X ⟶ A} {g : Y ⟶ B}
    [PathConnectedSpace Y] [PathConnectedSpace A] [PathConnectedSpace B]
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hg : TopCat.IsLocalCoefficientHomologyEquivalence g) :
    TopCat.IsLocalCoefficientHomologyEquivalence
      (TopCat.ofHom (f.hom.prodMap g.hom)) := by
  have h₁ := iso_allLocalCoefficients (TopCat.prodIsoProd X Y).symm
  have h₂ := hf.prodMap hg
  have h₃ := iso_allLocalCoefficients (TopCat.prodIsoProd A B)
  have he : TopCat.ofHom (f.hom.prodMap g.hom) =
      (TopCat.prodIsoProd X Y).inv ≫ prod.map f g ≫
        (TopCat.prodIsoProd A B).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change (f z.1, g z.2) =
      (TopCat.prodIsoProd A B).hom
        ((prod.map f g) ((TopCat.prodIsoProd X Y).inv z))
    rw [TopCat.prodIsoProd_hom_apply]
    apply Prod.ext
    · have h := ConcreteCategory.congr_hom (prod.map_fst f g)
        ((TopCat.prodIsoProd X Y).inv z)
      simpa only [ConcreteCategory.comp_apply,
        TopCat.prodIsoProd_inv_fst_apply] using h.symm
    · have h := ConcreteCategory.congr_hom (prod.map_snd f g)
        ((TopCat.prodIsoProd X Y).inv z)
      simpa only [ConcreteCategory.comp_apply,
        TopCat.prodIsoProd_inv_snd_apply] using h.symm
  rw [he]
  exact h₁.comp (h₂.comp h₃)

end IsLocalCoefficientHomologyEquivalence

end TopCat

end
