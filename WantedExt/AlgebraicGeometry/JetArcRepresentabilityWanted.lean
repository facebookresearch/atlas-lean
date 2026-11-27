/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.JetArcFunctors
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Representing the actual jet and formal arc functors

Ein--Mustata, arXiv:math/0612862, equation (2.1), Proposition 2.2,
Remark 2.4 and section 3. The coefficient equations and nilpotent-open
gluing of Proposition 2.2 work over any field; algebraic closure is not
used in that construction. The endpoint retains finite type over a field.

The functors, nilpotent discs and their restriction maps are already
fixed native constructions. The requests supply representing schemes
and geometric properties of those exact maps. An arc scheme is not
required to have finite type. This does not request generic scheme
gluing or generic polynomial-ring/derived-limit constructors again.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.JetArcRepresentability

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.JetArcFunctors

universe u

/-- Finite-type representation of the actual nilpotent-disc test functor. -/
public def_wanted jetScheme (k : Type u) [Field k] (X : OverBase k)
    (finite : IsFiniteTypeOverBase k X) (n : ℕ) :
    {M : JetModel k n X // IsFiniteTypeOverBase k M.scheme}

/-- Affineness of the fixed, quotient-normalized truncation morphism. -/
public theorem_wanted jetTruncationAffine (k : Type u) [Field k]
    (X : OverBase k) (finite : IsFiniteTypeOverBase k X) (m n : ℕ) (h : m ≤ n)
    (N : JetModel k n X) (M : JetModel k m X) :
    IsAffineHom (representedTruncation k h N M).left

/-- The formal compatible jet limit is represented by an actual scheme. -/
public def_wanted arcScheme (k : Type u) [Field k] (X : OverBase k)
    (finite : IsFiniteTypeOverBase k X) (jets : ∀ n : ℕ, JetModel k n X) : ArcModel k X

end WantedExt.AlgebraicGeometry.JetArcRepresentability
