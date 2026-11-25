/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.FundamentalGroupoid.SigmaSubtypeFullness
import Mathlib.Analysis.Convex.Contractible

/-!
# Tests for fullness of componentwise maps on sigma spaces

These client tests exercise the public sigma map and its fullness and
essential-surjectivity theorems on disconnected and empty indexed families.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology

namespace SigmaSubtypeFullnessTests

abbrev RealFamily (_ : Bool) : Type := ℝ

def realIdentity : ∀ i, C(RealFamily i, RealFamily i) :=
  fun _ => ContinuousMap.id ℝ

def sigmaRealIdentity : C((Σ i, RealFamily i), (Σ i, RealFamily i)) :=
  FundamentalGroupoid.SigmaSubtype.map RealFamily RealFamily realIdentity

example (i : Bool) (x : ℝ) :
    sigmaRealIdentity ⟨i, x⟩ = ⟨i, x⟩ := by
  simp [sigmaRealIdentity, realIdentity,
    FundamentalGroupoid.SigmaSubtype.map_apply]

local instance :
    (FundamentalGroupoid.map sigmaRealIdentity).Full :=
  FundamentalGroupoid.SigmaSubtype.mapFull RealFamily RealFamily realIdentity

local instance :
    (FundamentalGroupoid.map sigmaRealIdentity).EssSurj :=
  FundamentalGroupoid.SigmaSubtype.mapEssSurj RealFamily RealFamily realIdentity

example : (FundamentalGroupoid.map sigmaRealIdentity).Full := inferInstance

example : (FundamentalGroupoid.map sigmaRealIdentity).EssSurj := inferInstance

def falseZeroObject : FundamentalGroupoid (Σ i, RealFamily i) :=
  FundamentalGroupoid.mk (Sigma.mk false (0 : ℝ))

def trueZeroObject : FundamentalGroupoid (Σ i, RealFamily i) :=
  FundamentalGroupoid.mk (Sigma.mk true (0 : ℝ))

example (q : falseZeroObject ⟶ trueZeroObject) : False := by
  have h :=
    FundamentalGroupoid.SigmaComponent.hom_index_eq RealFamily q
  exact Bool.false_ne_true h

def sourceObject : FundamentalGroupoid (Σ i, RealFamily i) :=
  FundamentalGroupoid.mk (Sigma.mk false (0 : ℝ))

def targetObject : FundamentalGroupoid (Σ i, RealFamily i) :=
  FundamentalGroupoid.mk (Sigma.mk false (1 : ℝ))

def sameComponentArrow :
    (FundamentalGroupoid.map sigmaRealIdentity).obj sourceObject ⟶
      (FundamentalGroupoid.map sigmaRealIdentity).obj targetObject := by
  let p : Path (0 : ℝ) 1 := PathConnectedSpace.somePath 0 1
  exact Path.Homotopic.Quotient.mk
    (p.map (FundamentalGroupoid.SigmaComponent.inclusion RealFamily false).continuous)

example : sourceObject ≠ targetObject := by
  intro h
  have h' := congrArg
    (fun z : FundamentalGroupoid (Σ i, RealFamily i) => z.as.2) h
  exact zero_ne_one h'

example :
    let F := FundamentalGroupoid.map sigmaRealIdentity
    F.map (F.preimage sameComponentArrow) = sameComponentArrow :=
  (FundamentalGroupoid.map sigmaRealIdentity).map_preimage sameComponentArrow

abbrev EmptyFamily (_ : Empty) : Type := PUnit

def emptyComponentMap : ∀ i, C(EmptyFamily i, EmptyFamily i) :=
  fun i => i.elim

def emptySigmaMap : C((Σ i, EmptyFamily i), (Σ i, EmptyFamily i)) :=
  FundamentalGroupoid.SigmaSubtype.map EmptyFamily EmptyFamily emptyComponentMap

example : IsEmpty (Σ i, EmptyFamily i) := inferInstance

example :
    (FundamentalGroupoid.map emptySigmaMap).Full :=
  FundamentalGroupoid.SigmaSubtype.mapFull EmptyFamily EmptyFamily emptyComponentMap

example :
    (FundamentalGroupoid.map emptySigmaMap).EssSurj :=
  FundamentalGroupoid.SigmaSubtype.mapEssSurj EmptyFamily EmptyFamily emptyComponentMap

universe u v w

section MixedUniverses

variable {ι : Type u} (A : ι → Type w) (B : ι → Type v)
variable [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]

example (f : ∀ i, C(A i, B i)) :
    C((Σ i, A i), (Σ i, B i)) :=
  FundamentalGroupoid.SigmaSubtype.map A B f

example (f : ∀ i, C(A i, B i))
    [∀ i, PathConnectedSpace (A i)] [∀ i, SimplyConnectedSpace (B i)] :
    (FundamentalGroupoid.map
      (FundamentalGroupoid.SigmaSubtype.map A B f)).Full :=
  FundamentalGroupoid.SigmaSubtype.mapFull A B f

example (f : ∀ i, C(A i, B i))
    [∀ i, Nonempty (A i)] [∀ i, PathConnectedSpace (B i)] :
    (FundamentalGroupoid.map
      (FundamentalGroupoid.SigmaSubtype.map A B f)).EssSurj :=
  FundamentalGroupoid.SigmaSubtype.mapEssSurj A B f

end MixedUniverses

end SigmaSubtypeFullnessTests

end
