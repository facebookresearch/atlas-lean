/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE in ray intersection graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE;
S. Cabello, J. Cardinal and S. Langerman, "The clique problem in ray intersection graphs",
Discrete & Computational Geometry 50(3) (2013), 771-783, doi:10.1007/s00454-013-9538-5
(arXiv:1111.5986), Lemma 2.8 and Theorem 2.10.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RayIntersectionClique

/-- A ray: origin `(x, y)` and direction `(d, e)`, each integer encoded as a pair of naturals
standing for their difference. -/
abbrev Ray := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))

/-- An instance: the rays and the bound `K`. -/
abbrev RayIntersectionCliqueInstance := List Ray × ℕ

/-- The integer `p - q` encoded by the pair `(p, q)`. -/
def toInt (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - z.2

/-- The point set of the open ray with origin `(x, y)` and direction `(d, e)`:
`{(x + t d, y + t e) : t > 0}` (the origin itself is excluded). -/
def rayPoints (ρ : Ray) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, 0 < t ∧
    p = ((toInt ρ.1.1 : ℝ) + t * (toInt ρ.2.1 : ℝ), (toInt ρ.1.2 : ℝ) + t * (toInt ρ.2.2 : ℝ))}

/-- The intersection graph of the rays: one vertex per list entry, two distinct entries adjacent
when their rays share a point. -/
def Graph (i : RayIntersectionCliqueInstance) : SimpleGraph (Fin i.1.length) :=
  SimpleGraph.fromRel fun a b => (rayPoints (i.1.get a) ∩ rayPoints (i.1.get b)).Nonempty

/-- Well-formedness of an instance: every direction is nonzero, the rays are pairwise distinct
as point sets (a set of rays), and `0 < K ≤` the number of rays. -/
def WellFormed (i : RayIntersectionCliqueInstance) : Prop :=
  (∀ ρ ∈ i.1, toInt ρ.2.1 ≠ 0 ∨ toInt ρ.2.2 ≠ 0) ∧ (i.1.map rayPoints).Nodup ∧ 0 < i.2 ∧
    i.2 ≤ i.1.length

/-- The intersection graph has a clique of size `K` or more. -/
def RayIntersectionCliqueFeasible (i : RayIntersectionCliqueInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1.length))

open Classical in
/-- CLIQUE in ray intersection graphs as a decision problem over bitstrings. -/
noncomputable def rayIntersectionCliqueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RayIntersectionCliqueInstance) x with
  | some i => decide (WellFormed i ∧ RayIntersectionCliqueFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RayIntersectionClique
