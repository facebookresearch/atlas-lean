/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagSupport
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport

/-!
# The entire original terminal-supported coefficient

The native supported-face inverse takes the whole original coefficient
preimage. Its image is the same original chain, and its final flag contains
every selected vertex. Both original endpoint transports are explicit.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag

open SimplicialEnrichment

variable {n : ℕ} {q : SimplexCategoryᵒᵖ}

private instance {J : Type u} [LinearOrder J] (i j : J)
    (a b : SimplicialThickening.Path i j) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual original ordinal face selected by the entire last flag. -/
def operator (p : (coefficientObject.{u} n).obj q) :
    ⦋dimension p⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk (embedding p).toOrderHom

/-- The same whole original chain at the selected image endpoints. -/
def supportedCoefficient (p : (coefficientObject.{u} n).obj q) :
    (OrderEmbeddingFace.imageFace (liftedEmbedding p)
      (ULift.up.{u} 0) (ULift.up.{u} (Fin.last (dimension p))) : SSet.{u}).obj q :=
  ⟨(nerveMap (PathEndpointTransport.retarget (lifted_zero p).symm
      (lifted_last p).symm)).app q p, flag_supported p⟩

/-- The entire original coefficient under the native supported-face inverse. -/
def coefficient (p : (coefficientObject.{u} n).obj q) :
    (coefficientObject.{u} (dimension p)).obj q :=
  (OrderEmbeddingFace.faceIso (liftedEmbedding p)
    (ULift.up.{u} 0) (ULift.up.{u} (Fin.last (dimension p)))).inv.app q
      (supportedCoefficient p)

/-- Every selected coefficient flag is the whole original flag preimage. -/
theorem coefficient_flags (p : (coefficientObject.{u} n).obj q)
    (t : Fin (q.unop.len + 1)) :
    ((coefficient p).obj t).I = (liftedEmbedding p) ⁻¹' (p.obj t).I := rfl

/-- Every actual selected vertex occurs in the complete selected final flag. -/
theorem coefficient_last_full (p : (coefficientObject.{u} n).obj q) :
    ((coefficient p).obj (Fin.last q.unop.len)).I = Set.univ := by
  ext i
  constructor
  · intro _
    exact Set.mem_univ i
  · intro _
    change ULift.up.{u} (embedding p i.down) ∈ (p.obj (Fin.last q.unop.len)).I
    exact (mem_support p (embedding p i.down)).mp
      (Finset.orderEmbOfFin_mem (support p) (card_support p) i.down)

/-- The native original direct-image functor followed by the exact endpoint readbacks. -/
def imageFunctor (p : (coefficientObject.{u} n).obj q) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (dimension p + 1)))
      (ULift.up.{u} (Fin.last (dimension p))) ⥤
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1)))
      (ULift.up.{u} (Fin.last n)) :=
  SimplicialThickening.functorMap (liftedEmbedding p).toOrderHom
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (dimension p)))) ⋙
      PathEndpointTransport.retarget (lifted_zero p) (lifted_last p)

/-- The same actual whole coefficient image map at the original endpoints. -/
def imageMap (p : (coefficientObject.{u} n).obj q) :
    coefficientObject.{u} (dimension p) ⟶ coefficientObject.{u} n :=
  nerveMap (imageFunctor p)

/-- The entire selected coefficient maps back to the same original chain. -/
theorem image_coefficient (p : (coefficientObject.{u} n).obj q) :
    (imageMap p).app q (coefficient p) = p := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      obtain ⟨i, hi⟩ := flag_supported p t hx
      refine ⟨i, ?_, hi⟩
      change liftedEmbedding p i ∈ (p.obj t).I
      exact hi ▸ hx
  · intro i j f
    exact Subsingleton.elim _ _

/-- The original face map retains both original enriched coefficient endpoint transports. -/
theorem imageMap_operator (p : (coefficientObject.{u} n).obj q) :
    imageMap p =
      (coherentSimplexMap (operator p)).map
        (initial (dimension p)) (terminal (dimension p)) ≫
      eqToHom (congrArg₂
        (fun i j : coherentSimplex.{u} ⦋n⦌ => i ⟶[SSet.{u}] j)
        (congrArg SimplicialThickening.mk (lifted_zero p))
        (congrArg SimplicialThickening.mk (lifted_last p))) := by
  change nerveMap
      (SimplicialThickening.functorMap (liftedEmbedding p).toOrderHom
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (dimension p))))) ≫
      nerveMap (PathEndpointTransport.retarget (lifted_zero p) (lifted_last p)) = _
  exact congrArg (fun g =>
    nerveMap (SimplicialThickening.functorMap (liftedEmbedding p).toOrderHom
      (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (dimension p))))) ≫ g)
    (PathEndpointTransport.nerve_retarget (lifted_zero p) (lifted_last p))

end CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag
