/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NegativeHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarClosure

/-!
# Integer shifts of actual symmetric Omega targets

The target in nonnegative degree is the iterated scalar cotensor with the
original one-sphere. The target in negative degree is the iterated actual
function spectrum from the original first free zero-sphere. All of these
are functors on the same full enriched operator category.

The source's original delta identifies the next target with the scalar
loop of the current target in the original level homotopy category. The
comparison is constructed at every integer, including the transition
through degree zero, and is natural on complete original target maps.

The Omega predicate used throughout retains every original pair of
finite-bijection objects in the native stabilization family. This file
uses no homotopy-group criterion or stable model structure.

The constructions implement the target shifts in MMSS, *Model categories
of diagram spectra*, December 30, 1999 manuscript, Corollary 8.9 and
Theorem 8.12(vi), pages 27–28.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev scalarLoop := cotensor (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
  PointedCGWH.sphereOne.{u, v}

/-- The entire nonnegative iteration uses the actual enriched scalar-loop functor. -/
def loopIteration (n : ℕ) : C.{u, v} ⥤ C.{u, v} :=
  Functor.Iteration.iterate scalarLoop n

/-- The zero iteration retains every original object and map. -/
theorem loopIteration_zero : loopIteration.{u, v} 0 = 𝟭 C.{u, v} := rfl

/-- The full successor iteration applies the original scalar loop to the preceding functor. -/
theorem loopIteration_succ (n : ℕ) :
    loopIteration.{u, v} (n + 1) = loopIteration n ⋙ scalarLoop := rfl

/-- Negative iteration starts at the actual first function spectrum. -/
def negativeIteration : ℕ → C.{u, v} ⥤ C.{u, v}
  | 0 => NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping
  | n + 1 => negativeIteration n ⋙ NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping

/-- The entire normalized negative functor is the original first-free-zero-sphere iteration. -/
theorem negativeIteration_eq_original (n : ℕ) :
    negativeIteration.{u, v} n =
      NativeOmegaRecovery.NativeSymmetricDelooping.iteratedDelooping (n + 1) := by
  induction n with
  | zero =>
    exact (Functor.id_comp NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping).symm
  | succ n hn =>
    rw [negativeIteration, NativeOmegaRecovery.NativeSymmetricDelooping.iteratedDelooping_succ]
    exact congrArg (fun F => F ⋙ NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping) hn

/-- The source shift at every integer has the original scalar-loop or free-function carrier. -/
def target : ℤ → C.{u, v} ⥤ C.{u, v}
  | .ofNat n => loopIteration n
  | .negSucc n => negativeIteration n

/-- Nonnegative target degrees retain the whole original scalar-loop iteration. -/
theorem target_ofNat (n : ℕ) : target.{u, v} (n : ℤ) = loopIteration n := rfl

/-- Negative target degrees retain the whole original first-free-zero-sphere iteration. -/
theorem target_negSucc (n : ℕ) :
    target.{u, v} (Int.negSucc n) =
      NativeOmegaRecovery.NativeSymmetricDelooping.iteratedDelooping (n + 1) :=
  negativeIteration_eq_original n

/-- The normalized negative target retains the full original functor with its identity removed. -/
theorem target_negSucc_normalized (n : ℕ) :
    target.{u, v} (Int.negSucc n) = negativeIteration n := rfl

/-- Degree zero is the actual original target functor. -/
theorem target_zero : target.{u, v} 0 = 𝟭 C.{u, v} := rfl

/-- Degree minus one is the source's actual first-free-zero-sphere function spectrum. -/
theorem target_neg_one : target.{u, v} (-1) =
    NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping := rfl

/-- Degree one is the actual original scalar one-sphere cotensor. -/
theorem target_one : target.{u, v} 1 = scalarLoop := rfl

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
private theorem sphereCofibrant : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
  PointedCGWH.modelCategory.sphereOne_isCofibrant

attribute [local instance] sphereCofibrant

/-- Every actual scalar-loop iteration preserves the entire paired symmetric Omega condition. -/
theorem loopIteration_isOmega (n : ℕ) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Actual.SymmetricIsOmega ((loopIteration n).obj E) :=
  Functor.Iteration.preserves scalarLoop Actual.SymmetricIsOmega
    (fun X hX => NativeK.cotensor_isOmega Actual.symmetricFamily
      PointedCGWH.sphereOne X hX) n E hE

/-- Every integer target shift is Omega for the full original symmetric stabilization family. -/
theorem target_isOmega (q : ℤ) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Actual.SymmetricIsOmega ((target q).obj E) := by
  cases q with
  | ofNat n => exact loopIteration_isOmega (B := B) n E hE
  | negSucc n =>
    rw [target_negSucc]
    exact NativeOmegaRecovery.NativeSymmetricDelooping.iteratedDelooping_isOmega (n + 1) E hE

/-- Each shifted target has the original weak adjoint map at every source/added-degree pair. -/
theorem target_original_adjoint_weak (q : ℤ) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (n a : Operad.SmallFinBijGroupoid) :
    weakEquivalences PointedCGWH.{u, v}
      (NativeK.adjoint Actual.symmetricFamily (n, a) ((target q).obj E)) :=
  target_isOmega (B := B) q E hE (n, a)

private abbrev H := toHomotopyCategory C.{u, v}

/-- The normalized whole functor for the successor integer target. -/
def successorTarget : ℤ → C.{u, v} ⥤ C.{u, v}
  | .ofNat n => loopIteration (n + 1)
  | .negSucc 0 => 𝟭 C.{u, v}
  | .negSucc (n + 1) => negativeIteration n

omit B in
/-- Integer arithmetic identifies the complete successor-target functor, including all maps. -/
theorem target_successor (q : ℤ) : target.{u, v} (q + 1) = successorTarget q := by
  cases q with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hq : Int.negSucc (n + 1) + 1 = Int.negSucc n := rfl
      rw [hq]
      rfl

/-- Original Omega objects with their full original transformation category. -/
abbrev omegaProperty : ObjectProperty C.{u, v} := Actual.SymmetricIsOmega

/-- The actual successor comparison keeps the proven whole-functor arithmetic identification. -/
def successorNatIso (q : ℤ) :
    omegaProperty.{u, v}.ι ⋙ target (q + 1) ⋙ H.{u, v} ≅
      omegaProperty.{u, v}.ι ⋙ successorTarget q ⋙ H.{u, v} :=
  eqToIso (congrArg (fun F => omegaProperty.{u, v}.ι ⋙ F ⋙ H.{u, v}) (target_successor q))

/-- The normalized comparison uses the identity or the source's whole original delta. -/
def nextLoopIsoCore (q : ℤ) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    H.{u, v}.obj ((successorTarget q).obj E) ≅
      H.{u, v}.obj (scalarLoop.obj ((target q).obj E)) :=
  match q with
  | .ofNat _ => Iso.refl _
  | .negSucc 0 => NativeOmegaRecovery.NativeSymmetricDelooping.deltaHoIso E hE
  | .negSucc (n + 1) =>
    NativeOmegaRecovery.NativeSymmetricDelooping.deltaHoIso ((negativeIteration n).obj E)
      (target_isOmega (B := B) (Int.negSucc n) E hE)

/-- Every negative successor comparison retains the actual delta
of its entire preceding iteration. -/
theorem nextLoopIsoCore_negSucc_succ (n : ℕ) (E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    (nextLoopIsoCore (B := B) (Int.negSucc (n + 1)) E hE).hom =
      H.{u, v}.map (NativeOmegaRecovery.NativeSymmetricDelooping.delta.app
        ((negativeIteration n).obj E)) :=
  NativeOmegaRecovery.NativeSymmetricDelooping.deltaHoIso_hom
    ((negativeIteration n).obj E) (target_isOmega (B := B) (Int.negSucc n) E hE)

/-- Whole target maps commute with the original comparisons. -/
theorem nextLoopIsoCore_naturality (q : ℤ) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E') :
    H.{u, v}.map ((successorTarget q).map t) ≫ (nextLoopIsoCore (B := B) q E' hE').hom =
      (nextLoopIsoCore (B := B) q E hE).hom ≫
        H.{u, v}.map (scalarLoop.map ((target q).map t)) := by
  cases q with
  | ofNat n =>
    change H.{u, v}.map (scalarLoop.map ((loopIteration n).map t)) ≫
        𝟙 (H.{u, v}.obj (scalarLoop.obj ((loopIteration n).obj E'))) =
      𝟙 (H.{u, v}.obj (scalarLoop.obj ((loopIteration n).obj E))) ≫
        H.{u, v}.map (scalarLoop.map ((loopIteration n).map t))
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | negSucc n =>
    cases n with
    | zero =>
      change H.{u, v}.map t ≫
          H.{u, v}.map (NativeOmegaRecovery.NativeSymmetricDelooping.delta.app E') =
        H.{u, v}.map (NativeOmegaRecovery.NativeSymmetricDelooping.delta.app E) ≫
          H.{u, v}.map (NativeOmegaRecovery.NativeSymmetricDelooping.firstDeloopingLoop.map t)
      simpa only [Functor.map_comp] using H.{u, v}.congr_map
        (NativeOmegaRecovery.NativeSymmetricDelooping.delta_naturality t)
    | succ n =>
      simpa only [successorTarget, nextLoopIsoCore_negSucc_succ, target_negSucc_normalized,
        negativeIteration, NativeOmegaRecovery.NativeSymmetricDelooping.firstDeloopingLoop,
        Functor.comp_map, Functor.map_comp] using H.{u, v}.congr_map
        (NativeOmegaRecovery.NativeSymmetricDelooping.delta_naturality
          ((negativeIteration n).map t))

/-- The normalized comparison is a natural isomorphism on all original Omega targets. -/
def nextLoopCoreNatIso (q : ℤ) :
    omegaProperty.{u, v}.ι ⋙ successorTarget q ⋙ H.{u, v} ≅
      omegaProperty.{u, v}.ι ⋙ target q ⋙ scalarLoop ⋙ H.{u, v} :=
  NatIso.ofComponents (fun E => nextLoopIsoCore (B := B) q E.obj E.property)
    (fun t => nextLoopIsoCore_naturality (B := B) q _ _ t.hom)

/-- The complete original successor target is naturally the loop of the current target. -/
def nextLoopNatIso (q : ℤ) :
    omegaProperty.{u, v}.ι ⋙ target (q + 1) ⋙ H.{u, v} ≅
      omegaProperty.{u, v}.ι ⋙ target q ⋙ scalarLoop ⋙ H.{u, v} :=
  successorNatIso (B := B) q ≪≫ nextLoopCoreNatIso (B := B) q

/-- The component retains the whole successor-functor and original delta comparisons. -/
def nextLoopIso (q : ℤ) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    H.{u, v}.obj ((target (q + 1)).obj E) ≅
      H.{u, v}.obj (scalarLoop.obj ((target q).obj E)) :=
  (nextLoopNatIso (B := B) q).app ⟨E, hE⟩

/-- Both complete component functions use the actual arithmetic and original delta isomorphisms. -/
theorem nextLoopIso_original (q : ℤ) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    nextLoopIso (B := B) q E hE =
      (successorNatIso (B := B) q).app (⟨E, hE⟩ : omegaProperty.{u, v}.FullSubcategory) ≪≫
        nextLoopIsoCore (B := B) q E hE := rfl

/-- At degree minus one the complete arithmetic comparison is the original identity map. -/
theorem successorNatIso_neg_one_app_hom (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (successorNatIso (B := B) (-1)).hom.app
      (⟨E, hE⟩ : omegaProperty.{u, v}.FullSubcategory) = 𝟙 (H.{u, v}.obj E) := by
  simp only [successorNatIso, eqToIso.hom, eqToHom_refl, NatTrans.id_app]
  rfl

/-- The normalized degree minus one component retains the actual original delta function. -/
theorem nextLoopIsoCore_neg_one (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (nextLoopIsoCore (B := B) (-1) E hE).hom =
      H.{u, v}.map (NativeOmegaRecovery.NativeSymmetricDelooping.delta.app E) :=
  NativeOmegaRecovery.NativeSymmetricDelooping.deltaHoIso_hom E hE

/-- Degree minus one uses the whole original delta without an additional target action. -/
theorem nextLoopIso_neg_one (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (nextLoopIso (B := B) (-1) E hE).hom =
      H.{u, v}.map (NativeOmegaRecovery.NativeSymmetricDelooping.delta.app E) := by
  rw [nextLoopIso_original, Iso.trans_hom, Iso.app_hom,
    successorNatIso_neg_one_app_hom, nextLoopIsoCore_neg_one]
  exact Category.id_comp _

/-- The entire degree minus one component is the original native delta isomorphism. -/
theorem nextLoopIso_neg_one_iso (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    nextLoopIso (B := B) (-1) E hE =
      NativeOmegaRecovery.NativeSymmetricDelooping.deltaHoIso E hE := by
  apply Iso.ext
  exact nextLoopIso_neg_one (B := B) E hE

/-- All complete original Omega target maps retain the whole forward comparison square. -/
theorem nextLoopIso_naturality (q : ℤ) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E') :
    H.{u, v}.map ((target (q + 1)).map t) ≫ (nextLoopIso (B := B) q E' hE').hom =
      (nextLoopIso (B := B) q E hE).hom ≫
        H.{u, v}.map (scalarLoop.map ((target q).map t)) :=
  (nextLoopNatIso (B := B) q).hom.naturality
    (show (⟨E, hE⟩ : omegaProperty.{u, v}.FullSubcategory) ⟶ ⟨E', hE'⟩ from ⟨t⟩)

/-- The inverse comparison keeps all original target maps and both arithmetic endpoints. -/
theorem nextLoopIso_inv_naturality (q : ℤ) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E') :
    H.{u, v}.map (scalarLoop.map ((target q).map t)) ≫
        (nextLoopIso (B := B) q E' hE').inv =
      (nextLoopIso (B := B) q E hE).inv ≫ H.{u, v}.map ((target (q + 1)).map t) :=
  (nextLoopNatIso (B := B) q).inv.naturality
    (show (⟨E, hE⟩ : omegaProperty.{u, v}.FullSubcategory) ⟶ ⟨E', hE'⟩ from ⟨t⟩)

/-- Both entire comparison functions are inverse at every integer target degree. -/
theorem nextLoopIso_inverse_laws (q : ℤ) (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (nextLoopIso (B := B) q E hE).hom ≫ (nextLoopIso (B := B) q E hE).inv = 𝟙 _ ∧
      (nextLoopIso (B := B) q E hE).inv ≫ (nextLoopIso (B := B) q E hE).hom = 𝟙 _ :=
  ⟨(nextLoopIso (B := B) q E hE).hom_inv_id,
    (nextLoopIso (B := B) q E hE).inv_hom_id⟩

end PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets
