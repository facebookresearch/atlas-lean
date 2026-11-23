/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatRealizedHornOpenCover

/-!
# Tests for open-cover locality of realized horn lifting

Public-only consumers for local-to-global realized-horn lifting over open
covers.
-/

@[expose] public section

universe u v

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

namespace TopCatRealizedHornOpenCoverTests

section PublicAPI

example {E B : TopCat.{0}} {p : E ⟶ B}
    {ι : Type*} (U : ι → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U)
    (hp : ∀ i, TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom (p.hom.restrictPreimage (U i)))) :
    TopCat.realizedHornInclusions.{0}.rlp p :=
  TopCat.realizedHornRLP_of_openCover U hU hp

end PublicAPI

section AllUniverseAPI

example {E B : TopCat.{u}} {p : E ⟶ B}
    {ι : Type v} (U : ι → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U)
    (hp : ∀ i, TopCat.realizedHornInclusions.{u}.rlp
      (TopCat.ofHom (p.hom.restrictPreimage (U i)))) :
    TopCat.realizedHornInclusions.{u}.rlp p :=
  TopCat.realizedHornRLP_of_openCover U hU hp

end AllUniverseAPI

section Covers

private def oneCover (B : TopCat.{0}) :
    PUnit.{1} → TopologicalSpace.Opens B :=
  fun _ ↦ ⊤

private theorem oneCover_isOpenCover (B : TopCat.{0}) :
    TopologicalSpace.IsOpenCover (oneCover B) := by
  apply TopologicalSpace.IsOpenCover.mk
  simp [oneCover]

private def duplicateTopCover (B : TopCat.{0}) :
    Fin 2 → TopologicalSpace.Opens B :=
  fun _ ↦ ⊤

private theorem duplicateTopCover_isOpenCover (B : TopCat.{0}) :
    TopologicalSpace.IsOpenCover (duplicateTopCover B) := by
  apply TopologicalSpace.IsOpenCover.mk
  apply top_unique
  simpa [duplicateTopCover] using
    (le_iSup (duplicateTopCover B) (0 : Fin 2))

example {E B : TopCat.{0}} {p : E ⟶ B}
    (hp : TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage
          (⊤ : TopologicalSpace.Opens B)))) :
    TopCat.realizedHornInclusions.{0}.rlp p := by
  apply TopCat.realizedHornRLP_of_openCover
    (oneCover B) (oneCover_isOpenCover B)
  intro _
  exact hp

example {B : TopCat.{0}} (b : B) :
    b ∈ duplicateTopCover B 0 ∧
      b ∈ duplicateTopCover B 1 := by
  simp [duplicateTopCover]

example {E B : TopCat.{0}} {p : E ⟶ B}
    (hp : ∀ i : Fin 2, TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage (duplicateTopCover B i)))) :
    TopCat.realizedHornInclusions.{0}.rlp p :=
  TopCat.realizedHornRLP_of_openCover
    (duplicateTopCover B) (duplicateTopCover_isOpenCover B) hp

example {E B : TopCat.{u}} {p : E ⟶ B}
    (hp : ∀ _i : ℕ, TopCat.realizedHornInclusions.{u}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage
          (⊤ : TopologicalSpace.Opens B)))) :
    TopCat.realizedHornInclusions.{u}.rlp p := by
  let U : ℕ → TopologicalSpace.Opens B := fun _ ↦ ⊤
  apply TopCat.realizedHornRLP_of_openCover U
  · apply TopologicalSpace.IsOpenCover.mk
    simp [U]
  · intro i
    exact hp i

end Covers

section Horns

example {E B : TopCat.{0}} {p : E ⟶ B}
    (hp : TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage
          (⊤ : TopologicalSpace.Opens B)))) :
    HasLiftingProperty
      (SSet.toTop.map (SSet.horn 1 (0 : Fin 2)).ι) p := by
  have hglobal : TopCat.realizedHornInclusions.{0}.rlp p :=
    TopCat.realizedHornRLP_of_openCover
      (oneCover B) (oneCover_isOpenCover B) (fun _ ↦ hp)
  exact hglobal _
    (TopCat.horn_mem_realizedHornInclusions 1 (0 : Fin 2))

example {E B : TopCat.{0}} {p : E ⟶ B}
    (hp : TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage
          (⊤ : TopologicalSpace.Opens B)))) :
    HasLiftingProperty
      (SSet.toTop.map (SSet.horn 1 (1 : Fin 2)).ι) p := by
  have hglobal : TopCat.realizedHornInclusions.{0}.rlp p :=
    TopCat.realizedHornRLP_of_openCover
      (oneCover B) (oneCover_isOpenCover B) (fun _ ↦ hp)
  exact hglobal _
    (TopCat.horn_mem_realizedHornInclusions 1 (1 : Fin 2))

example {E B : TopCat.{0}} {p : E ⟶ B}
    (hp : ∀ i : Fin 2, TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage (duplicateTopCover B i)))) :
    HasLiftingProperty
      (SSet.toTop.map (SSet.horn 3 (1 : Fin 4)).ι) p := by
  have hglobal : TopCat.realizedHornInclusions.{0}.rlp p :=
    TopCat.realizedHornRLP_of_openCover
      (duplicateTopCover B) (duplicateTopCover_isOpenCover B) hp
  exact hglobal _
    (TopCat.horn_mem_realizedHornInclusions 3 (1 : Fin 4))

example {E B : TopCat.{u}} {p : E ⟶ B}
    (hp : TopCat.realizedHornInclusions.{u}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage
          (⊤ : TopologicalSpace.Opens B)))) :
    HasLiftingProperty
      (SSet.toTop.map (SSet.horn.{u} 1 (0 : Fin 2)).ι) p := by
  let U : PUnit.{v + 1} → TopologicalSpace.Opens B := fun _ ↦ ⊤
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.mk
    simp [U]
  have hglobal : TopCat.realizedHornInclusions.{u}.rlp p :=
    TopCat.realizedHornRLP_of_openCover U hU (fun _ ↦ hp)
  exact hglobal _
    (TopCat.horn_mem_realizedHornInclusions 1 (0 : Fin 2))

end Horns

section Boundaries

example {B : TopCat.{0}} (b : B)
    (U : PEmpty → TopologicalSpace.Opens B) :
    ¬TopologicalSpace.IsOpenCover U := by
  intro hU
  obtain ⟨i, _⟩ := hU.exists_mem b
  exact i.elim

example {B : TopCat.{u}} (b : B)
    (U : PEmpty → TopologicalSpace.Opens B) :
    ¬TopologicalSpace.IsOpenCover U := by
  intro hU
  obtain ⟨i, _⟩ := hU.exists_mem b
  exact i.elim

example {E B : TopCat.{0}} {p : E ⟶ B}
    (hp : TopCat.realizedHornInclusions.{0}.rlp
      (TopCat.ofHom
        (p.hom.restrictPreimage
          (⊤ : TopologicalSpace.Opens B)))) :
    TopCat.realizedHornInclusions.{0}.rlp p := by
  fail_if_success
    let _ : LocallyCompactSpace E := inferInstance
  fail_if_success
    let _ : LocallyCompactSpace B := inferInstance
  fail_if_success
    let _ : ConnectedSpace E := inferInstance
  fail_if_success
    let _ : ConnectedSpace B := inferInstance
  exact TopCat.realizedHornRLP_of_openCover
    (oneCover B) (oneCover_isOpenCover B) (fun _ ↦ hp)

end Boundaries

section UniverseBoundary

variable
  (E₁ B₁ : TopCat.{1}) (p₁ : E₁ ⟶ B₁)
  (U₁ : PUnit.{2} → TopologicalSpace.Opens B₁)
  (hU₁ : TopologicalSpace.IsOpenCover U₁)
  (hp₁ : ∀ i, TopCat.realizedHornInclusions.{1}.rlp
    (TopCat.ofHom (p₁.hom.restrictPreimage (U₁ i))))

example : TopCat.realizedHornInclusions.{1}.rlp p₁ :=
  TopCat.realizedHornRLP_of_openCover U₁ hU₁ hp₁

end UniverseBoundary

#print axioms TopCat.realizedHornRLP_of_openCover

end TopCatRealizedHornOpenCoverTests

end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
