/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalLoopFiberComparison

/-!
# The SAME original connecting function represented by any whole original lift

An entire original pointed sequence hom from the original based-path
fibration to S, with its actual base map equal to the original identity,
represents S.connectingMap through its literal original fiberMap in every
degree, including zero.  Every original sequence square is preserved on
homotopy.  Independence here concerns these induced homotopy functions;
no equality between independently selected strict lifts is inferred.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen

namespace SSet.OriginalConnectingLiftRepresentationGeometry

open SSet.OriginalBasedPathConnectingGeometry
open SSet.OriginalBasedPathLoopComparisonGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint loopConnectingEquiv)

private theorem originalPiMap_of_whole_identity {X : SSet.{u}}
    (f : X ⟶ X) (x : X _⦋0⦌) (h : f.app _ x = x) (hf : f = 𝟙 X)
    (n : ℕ) (q : SSet.KanComplex.π n X x) : SSet.KanComplex.π.map f h n q = q := by
  subst f
  exact SSet.KanComplex.π.map_id_apply q

/-- The full map from an arbitrary whole original lift is its SAME literal original fiberMap. -/
def originalConnectingLoopMapOfLift (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S) :
    loopSpace S.B S.b ⟶ S.fiber := L.fiberMap

/-- Every entire original lift retains its SAME complete original total inclusion square. -/
@[reassoc]
theorem originalConnectingLoopMapOfLift_projection (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S) :
    originalConnectingLoopMapOfLift S L ≫ S.fiberIncl =
      SSet.loopSpaceIncl S.B S.b ≫ L.totalMap := L.fiberMap_ι

/-- Every entire original lift retains both SAME original selected loop and fiber vertices. -/
theorem originalConnectingLoopMapOfLift_point (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S) :
    (originalConnectingLoopMapOfLift S L).app _ (originalLoopPoint S.B S.b) =
      S.fiberPoint := L.fiberMap_app_basePoint

/-- Every entire original lift retains the whole SAME original constant-point map. -/
theorem originalConnectingLoopMapOfLift_point_map {A : SSet.{u}}
    (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S) :
    SSet.const (X := A) (originalLoopPoint S.B S.b) ≫
        originalConnectingLoopMapOfLift S L = SSet.const S.fiberPoint :=
  (SSet.const_comp _ _).trans (congrArg (fun x => SSet.const (X := A) x)
    (originalConnectingLoopMapOfLift_point S L))

/-- Every full original lift over the SAME original identity represents the original connecting
function after the SAME original degree shift, including degree zero. -/
theorem originalConnectingLoopMapOfLift_pi_then_shift (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S)
    (hL : L.baseMap = 𝟙 S.B) (n : ℕ) (q : SSet.KanComplex.π (n + 1) S.B S.b) :
    SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
        (originalConnectingLoopMapOfLift_point S L) n (loopConnectingEquiv n S.B S.b q) =
      S.connectingMap n q := by
  have h := SSet.FibrationSequence.connectingMap_naturality L q
  exact h.trans (congrArg (S.connectingMap n)
    (originalPiMap_of_whole_identity L.baseMap S.b L.base_pt hL (n + 1) q))

/-- Every full original lift over the SAME identity retains the original inverse shift function. -/
theorem originalConnectingLoopMapOfLift_pi (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S)
    (hL : L.baseMap = 𝟙 S.B) (n : ℕ)
    (q : SSet.KanComplex.π n (loopSpace S.B S.b) (originalLoopPoint S.B S.b)) :
    SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
        (originalConnectingLoopMapOfLift_point S L) n q =
      S.connectingMap n ((loopConnectingEquiv n S.B S.b).symm q) :=
  (congrArg (SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
    (originalConnectingLoopMapOfLift_point S L) n)
    ((loopConnectingEquiv n S.B S.b).apply_symm_apply q).symm).trans
      (originalConnectingLoopMapOfLift_pi_then_shift S L hL n
        ((loopConnectingEquiv n S.B S.b).symm q))

/-- The entire original all-degree representation is one whole function equality. -/
theorem originalConnectingLoopMapOfLift_pi_function (S : SSet.FibrationSequence.{u})
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S)
    (hL : L.baseMap = 𝟙 S.B) (n : ℕ) :
    SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
        (originalConnectingLoopMapOfLift_point S L) n =
      S.connectingMap n ∘ (loopConnectingEquiv n S.B S.b).symm :=
  funext (originalConnectingLoopMapOfLift_pi S L hL n)

/-- Any two whole actual original identity-base lifts give the SAME whole induced homotopy
function.  Their strict total or fiber maps are not identified. -/
theorem originalConnectingLoopMapOfLift_pi_independent (S : SSet.FibrationSequence.{u})
    (L M : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S)
    (hL : L.baseMap = 𝟙 S.B) (hM : M.baseMap = 𝟙 S.B) (n : ℕ) :
    SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
        (originalConnectingLoopMapOfLift_point S L) n =
      SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S M)
        (originalConnectingLoopMapOfLift_point S M) n :=
  (originalConnectingLoopMapOfLift_pi_function S L hL n).trans
    (originalConnectingLoopMapOfLift_pi_function S M hM n).symm

/-- Every whole original sequence square preserves the homotopy representation from arbitrary
entire original identity-base lifts on both sides. -/
theorem originalConnectingLoopMapOfLift_pi_naturality {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T)
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S)
    (M : SSet.FibrationSequenceHom (loopFibrationSequence T.B T.b) T)
    (hL : L.baseMap = 𝟙 S.B) (hM : M.baseMap = 𝟙 T.B) (n : ℕ)
    (q : SSet.KanComplex.π n (loopSpace S.B S.b) (originalLoopPoint S.B S.b)) :
    SSet.KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n
        (SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
          (originalConnectingLoopMapOfLift_point S L) n q) =
      SSet.KanComplex.π.map (originalConnectingLoopMapOfLift T M)
        (originalConnectingLoopMapOfLift_point T M) n
          (SSet.KanComplex.π.map (SSet.loopSpaceMap f.baseMap f.base_pt)
            (originalLoopSpaceMap_point f.baseMap f.base_pt) n q) := by
  let r := (loopConnectingEquiv n S.B S.b).symm q
  have hOriginal := SSet.FibrationSequence.connectingMap_naturality f r
  have hSource := congrArg (SSet.KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n)
    (originalConnectingLoopMapOfLift_pi S L hL n q)
  have hTarget := originalConnectingLoopMapOfLift_pi T M hM n
    (SSet.KanComplex.π.map (SSet.loopSpaceMap f.baseMap f.base_pt)
      (originalLoopSpaceMap_point f.baseMap f.base_pt) n q)
  exact hSource.trans (hOriginal.trans ((congrArg (T.connectingMap n)
    (SSet.LoopShiftOriginalGeometry.loopConnectingEquiv_symm_naturality
      f.baseMap f.base_pt n q)).trans hTarget.symm))

/-- The full naturality square from arbitrary actual original lifts is retained as whole
all-degree functions, with the SAME source and target comparisons. -/
theorem originalConnectingLoopMapOfLift_pi_naturality_function
    {S T : SSet.FibrationSequence.{u}} (f : SSet.FibrationSequenceHom S T)
    (L : SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S)
    (M : SSet.FibrationSequenceHom (loopFibrationSequence T.B T.b) T)
    (hL : L.baseMap = 𝟙 S.B) (hM : M.baseMap = 𝟙 T.B) (n : ℕ) :
    SSet.KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n ∘
        SSet.KanComplex.π.map (originalConnectingLoopMapOfLift S L)
          (originalConnectingLoopMapOfLift_point S L) n =
      SSet.KanComplex.π.map (originalConnectingLoopMapOfLift T M)
        (originalConnectingLoopMapOfLift_point T M) n ∘
          SSet.KanComplex.π.map (SSet.loopSpaceMap f.baseMap f.base_pt)
            (originalLoopSpaceMap_point f.baseMap f.base_pt) n :=
  funext (originalConnectingLoopMapOfLift_pi_naturality f L M hL hM n)

/-- The preceding actual selected whole lift is literally the original earlier connecting map. -/
theorem originalConnectingLoopMapOfLift_selected (S : SSet.FibrationSequence.{u}) :
    originalConnectingLoopMapOfLift S (basedPathLiftSequenceHom S) = connectingLoopMap S := rfl

end SSet.OriginalConnectingLiftRepresentationGeometry
