/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairPerfectComplexes
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Actual supertrace and trace-free perfect-complex sources

Each term trace is fixed by the matrix trace in every finite affine
frame. The degree-zero supertrace is their signed finite sum. Scalars
are the actual internal-Hom multiplication maps. The cochain trace and
scalar maps are normalized to these fixed maps.

The trace-free object is the actual homotopy fibre of that trace.
Its inclusion uses the native mapping-cone projection in every degree.
No arbitrary trace-free derived object or obstruction theory occurs.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, §2.3,
the trace/identity splitting before Lemma 2.10.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairTraceModels

open CategoryTheory CategoryTheory.Limits Opposite Module
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries BundleTrace
open StablePairInternalHomMaps StablePairPerfectComplexes
attribute [local instance] HasDerivedCategory.standard

variable {Y : Scheme}

/-- Trace in all actual finite affine frames, allowing variable local rank. -/
structure LocalBundleTrace (E : Y.Modules) where
  map : endSheaf Y E ⟶ structureModule Y
  normalized : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (r : ℕ)
    (b : Module.Basis (Fin r) (Y.ringCatSheaf.obj.obj (op U)) (E.val.obj (op U)))
    (a : (endSheaf Y E).val.obj (op U)),
    (map.val.app (op U)).hom a =
      (LinearMap.toMatrix b b (localEndomorphism Y E U a)).trace

variable (A : FiniteComplex Y)

/-- The actual supertrace on the source degree-zero sheaf. -/
def superTrace (T : ∀ i : Indices A, LocalBundleTrace (A.cochain.X i.val)) :
    endDegree A 0 ⟶ structureModule Y :=
  ∑ i : Indices A, (Int.negOnePow i.val).val •
    (Pi.π (fun j : Indices A =>
      homSheaf Y (A.cochain.X j.val) (A.cochain.X (j.val+0))) i ≫
      postcompose (A.cochain.XIsoOfEq (p := i.val+0) (q := i.val) (by omega)).hom ≫
        (T i).map)

/-- Scalars act through the identity of every actual complex term. -/
def scalarIdentity : structureModule Y ⟶ endDegree A 0 :=
  Pi.lift (fun i : Indices A =>
    scalarEndomorphisms Y (A.cochain.X i.val) ≫
      postcompose (A.cochain.XIsoOfEq (p := i.val+0) (q := i.val) (by omega)).inv)

/-- A genuine cochain trace and scalar inclusion, with their original maps fixed. -/
structure TracePacket (h : EndSquaredZero A) where
  term : ∀ i : Indices A, LocalBundleTrace (A.cochain.X i.val)
  trace : endComplex A h ⟶
    (CochainComplex.singleFunctor Y.Modules 0).obj (structureModule Y)
  trace_normalized : trace.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (structureModule Y)).hom =
    superTrace A term
  scalar : (CochainComplex.singleFunctor Y.Modules 0).obj (structureModule Y) ⟶ endComplex A h
  scalar_normalized : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (structureModule Y)).inv ≫
    scalar.f 0 = scalarIdentity A

/-- The actual homotopy fibre of the native cochain trace. -/
def traceFreeComplex {h : EndSquaredZero A} (T : TracePacket A h) : CochainComplex Y.Modules ℤ :=
  (CochainComplex.mappingCone T.trace)⟦(-1 : ℤ)⟧

def traceFreeDerived {h : EndSquaredZero A} (T : TracePacket A h) : DerivedCategory Y.Modules :=
  DerivedCategory.Q.obj (traceFreeComplex A T)

/-- The actual inclusion of this trace fibre is fixed in every cochain degree. -/
structure TraceFreeInclusion {h : EndSquaredZero A} (T : TracePacket A h) where
  map : traceFreeComplex A T ⟶ endComplex A h
  normalized : ∀ i : ℤ, map.f i =
    ((CochainComplex.mappingCone T.trace).shiftFunctorObjXIso (-1) i (i-1) (by omega)).hom ≫
      (CochainComplex.mappingCone.fst T.trace).val.v (i-1) i (by omega)

end MathlibExt.AlgebraicGeometry.StablePairTraceModels
