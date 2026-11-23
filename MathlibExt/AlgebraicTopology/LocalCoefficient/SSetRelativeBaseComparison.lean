/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetBaseCoherence
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The original relative coefficient map through an ambient comparison

The original map over a fixed coefficient base gives the actual map on
cokernels. When its ambient leg is a quasi-isomorphism, the stock vertical
cokernel theorem proves this relative map is a quasi-isomorphism. Both
horizontal monomorphisms are derived from the actual simplicial inclusions.
No relative excision or coefficient flatness is an input. A cover supplies
the ambient quasi-isomorphism in a separate, computed application.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] {V B T : SSet.{uX}}

private local instance localCoefficientComplexHasHomology
    (K : ChainComplex (ModuleCat.{max uR uX} R) ℕ) :
    ∀ n : ℕ, HomologicalComplex.HasHomology K n := fun _ => inferInstance

/-- The actual relative quotient comparison for a map of spaces over T.
Its left leg is the identity, and its right leg is the original ambient
coefficient pullback map. -/
public def localCoefficientRelativeBaseMap
    (f : V ⟶ B) (b : B ⟶ T) (v : V ⟶ T) (hv : v = f ≫ b)
    (L : SSet.LocalSystem R T) :
    cokernel (localCoefficientChainMapOver f b v hv L) ⟶
      cokernel (localCoefficientPullbackChainMap v L) := by
  let a := localCoefficientChainMapOver f b v hv L
  let c := localCoefficientPullbackChainMap v L
  let m := localCoefficientPullbackChainMap b L
  have hs : (𝟙 _) ≫ c = a ≫ m := by
    rw [Category.id_comp]
    exact (localCoefficientChainMapOver_comp f b v hv L).symm
  exact cokernel.map a c (𝟙 _) m hs.symm

/-- The computed relative map retains the whole original quotient square. -/
@[reassoc]
public theorem localCoefficientRelativeBaseMap_π
    (f : V ⟶ B) (b : B ⟶ T) (v : V ⟶ T) (hv : v = f ≫ b)
    (L : SSet.LocalSystem R T) :
    cokernel.π (localCoefficientChainMapOver f b v hv L) ≫
        localCoefficientRelativeBaseMap f b v hv L =
      localCoefficientPullbackChainMap b L ≫
        cokernel.π (localCoefficientPullbackChainMap v L) := by
  unfold localCoefficientRelativeBaseMap
  exact cokernel.π_desc _ _ _

/-- The actual ambient quasi-isomorphism induces a quasi-isomorphism on
the actual relative quotients. This is the stock vertical cokernel theorem,
with derived horizontal monicity and the original source triangle. -/
public theorem localCoefficientRelativeBaseMap_quasiIso
    (f : V ⟶ B) [Mono f] (b : B ⟶ T) [Mono b]
    (v : V ⟶ T) (hv : v = f ≫ b) (L : SSet.LocalSystem R T)
    (hb : QuasiIso (localCoefficientPullbackChainMap b L)) :
    QuasiIso (localCoefficientRelativeBaseMap f b v hv L) := by
  let K := localCoefficientChainComplex (L.pullback v)
  let D := localCoefficientChainComplex (L.pullback b)
  let E := localCoefficientChainComplex L
  let a : K ⟶ D := localCoefficientChainMapOver f b v hv L
  let c : K ⟶ E := localCoefficientPullbackChainMap v L
  let m : D ⟶ E := localCoefficientPullbackChainMap b L
  let : Mono v := by
    rw [hv]
    infer_instance
  let : Mono a := localCoefficientChainMapOver_mono f b v hv L
  let : Mono c := localCoefficientPullbackChainMap_mono_of_mono v L
  let A : (MorphismProperty.monomorphisms
      (ChainComplex (ModuleCat.{max uR uX} R) ℕ)).Arrow ⊤ ⊤ :=
    MorphismProperty.Arrow.mk a (inferInstance : Mono a)
  let B' : (MorphismProperty.monomorphisms
      (ChainComplex (ModuleCat.{max uR uX} R) ℕ)).Arrow ⊤ ⊤ :=
    MorphismProperty.Arrow.mk c (inferInstance : Mono c)
  have hs : (𝟙 K) ≫ c = a ≫ m := by
    rw [Category.id_comp]
    exact (localCoefficientChainMapOver_comp f b v hv L).symm
  let φ : A ⟶ B' := MorphismProperty.Arrow.homMk (𝟙 K) m hs
  have hφleft : φ.left = (𝟙 K : K ⟶ K) := rfl
  have hφright : φ.right = m := rfl
  have hid : QuasiIso (𝟙 K : K ⟶ K) := inferInstance
  have hm : QuasiIso m := hb
  have hleft : QuasiIso φ.left := hφleft.symm ▸ hid
  have hright : QuasiIso φ.right := hφright.symm ▸ hm
  let F := MorphismProperty.Arrow.forget
    (MorphismProperty.monomorphisms
      (ChainComplex (ModuleCat.{max uR uX} R) ℕ)) ⊤ ⊤
  let q : cokernel a ⟶ cokernel c :=
    (F ⋙ Limits.coker (ChainComplex (ModuleCat.{max uR uX} R) ℕ)).map φ
  have hq : QuasiIso q :=
    HomologicalComplex.HomologySequence.quasiIso_coker_map
      (C := ModuleCat.{max uR uX} R) (c := ComplexShape.down ℕ) φ hleft hright
  let ψ : Arrow.mk a ⟶ Arrow.mk c := F.map φ
  have hqπ : cokernel.π a ≫ q = m ≫ cokernel.π c :=
    ((Limits.coker.π (ChainComplex (ModuleCat.{max uR uX} R) ℕ)).naturality ψ).symm
  have hqMap : q = localCoefficientRelativeBaseMap f b v hv L := by
    apply (cancel_epi (cokernel.π a)).1
    exact hqπ.trans (localCoefficientRelativeBaseMap_π f b v hv L).symm
  exact hqMap ▸ hq

end SSet

end
