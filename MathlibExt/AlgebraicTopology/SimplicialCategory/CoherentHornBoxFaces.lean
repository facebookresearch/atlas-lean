/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOutsideIntervals
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapAlgebra

/-!
# Actual positive and negative Hom-box pieces of a coherent horn

The source pieces are the original composition and omitted-vertex faces
of the outer coherent Hom. Their maps are constructed from the actual
supplied endpoint and negative horn faces, retaining individual objects
and the two outer endpoint labels. No compatibility or box-map outcome
is passed in as data.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornBoxFaces
open SimplicialEnrichment
variable {n : ℕ}

/-- The same original outer coherent Hom, with vertices zero and the last original vertex. -/
abbrev outerHom (n : ℕ) : SSet.{u} :=
  nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up.{u} (Fin.last
    (n + 2))))

/-- The original strict interior labels of the outer coherent Hom. -/
abbrev Interior (n : ℕ) := IntervalHom.Interior (ULift.up.{u} (0 : Fin (n + 3)))
  (ULift.up.{u} (Fin.last (n + 2)))

/-- Read the same original finite vertex label of a supplied interior point. -/
abbrev vertex (b : Interior.{u} n) : Fin (n + 3) := b.val.down

/-- An original interior label is distinct from the first original endpoint. -/
theorem vertex_ne_zero (b : Interior.{u} n) : vertex b ≠ 0 :=
  ne_of_gt (show (0 : Fin (n + 3)) < vertex b from b.property.1)

/-- An original interior label is distinct from the last original endpoint. -/
theorem vertex_ne_last (b : Interior.{u} n) : vertex b ≠ Fin.last (n + 2) :=
  ne_of_lt (show vertex b < Fin.last (n + 2) from b.property.2)

/-- The actual inner horn index, retained as its individual original interior vertex. -/
def inner (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) : Interior.{u} n :=
  ⟨ULift.up i, Fin.pos_iff_ne_zero.mpr hi₀, Fin.lt_last_iff_ne_last.mpr hiₙ⟩

/-- All original positive labels and the original negative labels different from the actual
missing index. -/
abbrev Index (i : Fin (n + 3)) := Interior.{u} n ⊕ {k : Interior.{u} n // vertex k ≠ i}

/-- The actual original Hom-box face at its supplied positive or negative label. -/
def face (i : Fin (n + 3)) : Index.{u} i → (outerHom.{u} n).Subcomplex
  | .inl b => CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))
  | .inr k => HomBoxDecomposition.negative (ULift.up 0) k.val.val (ULift.up (Fin.last (n + 2)))

/-- These actual original positive and negative faces cover precisely the distinguished
coherent Hom box. -/
theorem cover (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) :
    (⨆ x : Index.{u} i, face i x) = HomOpenBox.subcomplex (show (ULift.up.{u} (0 : Fin (n
      + 3))) ≤ ULift.up
      (Fin.last (n + 2)) from Fin.zero_le _) (inner i hi₀ hiₙ) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    rcases x with b | k
    · exact HomBoxDecomposition.positive_le (show (ULift.up.{u} (0 : Fin (n + 3))) ≤
      ULift.up (Fin.last (n +
      2)) from Fin.zero_le _) (inner i hi₀ hiₙ) b
    · apply HomBoxDecomposition.negative_le (show (ULift.up.{u} (0 : Fin (n + 3))) ≤
      ULift.up (Fin.last (n +
      2)) from Fin.zero_le _) (inner i hi₀ hiₙ) k.val
      intro h
      exact k.property (congrArg vertex h)
  · intro q p hp
    obtain hp | ⟨t, hp | hp⟩ := (HomBoxDecomposition.mem_iff (show (ULift.up.{u} (0 :
      Fin (n + 3))) ≤
      ULift.up (Fin.last (n + 2)) from Fin.zero_le _) (inner i hi₀ hiₙ) p).mp hp
    · exact (le_iSup (fun x : Index.{u} i => face i x) (.inl (inner i hi₀ hiₙ))) q hp
    · have ht : vertex t.val ≠ i := by
        intro h
        exact t.property (Subtype.ext (ULift.ext h))
      exact (le_iSup (fun x : Index.{u} i => face i x) (.inr ⟨t.val, ht⟩)) q hp
    · exact (le_iSup (fun x : Index.{u} i => face i x) (.inl t.val)) q hp

variable {C : Carrier.{u}} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- The actual whole original short Hom from the first endpoint to the supplied middle vertex. -/
def leftMap (b : Interior.{u} n) :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3))) b.val) ⟶
      (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (vertex b)) :=
  HornOutsideIntervals.homMap f hi₀ hiₙ 0 (vertex b) (Fin.zero_le _) (Or.inr (vertex_ne_last b))

/-- The actual whole original short Hom from the same middle vertex to the last endpoint. -/
def rightMap (b : Interior.{u} n) :
    nerve (SimplicialThickening.Path b.val (ULift.up.{u} (Fin.last (n + 2)))) ⟶
      (HornFaces.object f (vertex b) ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) :=
  HornOutsideIntervals.homMap f hi₀ hiₙ (vertex b) (Fin.last (n + 2)) (Fin.le_last _)
    (Or.inl (vertex_ne_zero b))

/-- The actual original positive-face map, from the two supplied short Hom maps and actual
target composition. -/
def positiveMap (b : Interior.{u} n) :
    (CompositionFace.positive (ULift.up.{u} (0 : Fin (n + 3))) b.val (ULift.up.{u} (Fin.last
      (n + 2))) : SSet.{u}) ⟶
      (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) :=
  (CompositionFace.positiveIso (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))).inv ≫
    (leftMap f hi₀ hiₙ b ⊗ₘ rightMap f hi₀ hiₙ b) ≫
      eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (vertex b))
        (HornFaces.object f (Fin.last (n + 2)))

/-- The positive piece reads back the whole actual target composition of the same two
original short Hom maps. -/
theorem positiveMap_readback (b : Interior.{u} n) :
    (CompositionFace.positiveIso (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))).hom ≫
      positiveMap f hi₀ hiₙ b =
      (leftMap f hi₀ hiₙ b ⊗ₘ rightMap f hi₀ hiₙ b) ≫
        eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (vertex b))
          (HornFaces.object f (Fin.last
          (n + 2))) := by
  let E := CompositionFace.positiveIso (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))
  let M := (leftMap f hi₀ hiₙ b ⊗ₘ rightMap f hi₀ hiₙ b) ≫
    eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (vertex b)) (HornFaces.object
      f (Fin.last (n + 2)))
  exact (Category.assoc E.hom E.inv M).symm.trans
    ((congrArg (fun h => h ≫ M) E.hom_inv_id).trans (Category.id_comp _))

/-- The first original vertex of a supplied nonendpoint face remains the first original endpoint. -/
theorem source_zero (k : Interior.{u} n) : (vertex k).succAbove (0 : Fin (n + 2)) = 0 :=
  Fin.succAbove_ne_zero_zero (vertex_ne_zero k)

/-- The last original vertex of that same face remains the last original endpoint. -/
theorem target_last (k : Interior.{u} n) : (vertex k).succAbove (Fin.last (n + 1)) =
  Fin.last (n + 2) :=
  Fin.succAbove_ne_last_last (vertex_ne_last k)

/-- The genuine supplied negative-face Hom chart, with both original outer endpoints
identified explicitly. -/
def negativeChart (k : Interior.{u} n) :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u}
      (Fin.last (n + 1)))) ≅
      HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) :=
  OrdinalFace.negativeIso (vertex k) (ULift.up 0) (ULift.up (Fin.last (n + 1))) ≪≫
    eqToIso (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
      (HomBoxDecomposition.negative a k.val b : SSet.{u}))
      (ULift.ext (source_zero k)) (ULift.ext (target_last k)))

/-- The actual negative-face map from its supplied enriched face functor, retaining the two
original outer objects. -/
def negativeMap (k : Interior.{u} n) (hk : vertex k ≠ i) :
    (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) : SSet.{u}) ⟶
      (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) :=
  (negativeChart k).inv ≫ HornHomFaces.retargetMap (HornFaces.faceFunctor f (vertex k) hk)
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))
    ((HornFaces.faceFunctor_obj f (vertex k) hk (.mk (ULift.up 0))).trans
      (congrArg (HornFaces.object f) (source_zero k)))
    ((HornFaces.faceFunctor_obj f (vertex k) hk (.mk (ULift.up (Fin.last (n + 1))))).trans
      (congrArg (HornFaces.object f) (target_last k)))

/-- The negative piece reads back the entire original supplied face Hom map with the two
outer endpoint transports. -/
theorem negativeMap_readback (k : Interior.{u} n) (hk : vertex k ≠ i) :
    (negativeChart k).hom ≫ negativeMap f k hk =
      HornHomFaces.retargetMap (HornFaces.faceFunctor f (vertex k) hk)
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))
        ((HornFaces.faceFunctor_obj f (vertex k) hk (.mk (ULift.up 0))).trans
          (congrArg (HornFaces.object f) (source_zero k)))
        ((HornFaces.faceFunctor_obj f (vertex k) hk (.mk (ULift.up (Fin.last (n + 1))))).trans
          (congrArg (HornFaces.object f) (target_last k))) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ _) (negativeChart k).hom_inv_id).trans (Category.id_comp _))

/-- The actual family of whole face maps constructed from the supplied original horn data. -/
def maps : (x : Index.{u} i) → (face i x : SSet.{u}) ⟶
    (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2)))
  | .inl b => positiveMap f hi₀ hiₙ b
  | .inr k => negativeMap f k.val k.property

end CategoryTheory.CoherentRealization.HornBoxFaces
