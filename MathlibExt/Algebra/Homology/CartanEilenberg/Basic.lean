/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.BoundaryCycles
public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe

/-!
# Cartan–Eilenberg resolution data

Let C be abelian and L a nonnegative chain complex. Chosen projective resolutions PBⱼ of
outgoing boundaries and PHⱼ of homology give a horseshoe resolution PCⱼ of cycles through 0 →
Bⱼ₊₁⁽out⁾ → Zⱼ(L) → Hⱼ(L) → 0. A second horseshoe gives a term resolution PTⱼ through 0 → Zⱼ(L)
→ Lⱼ → Bⱼ⁽out⁾ → 0, using the same PCⱼ as its left endpoint.

The data includes the selected biproduct coordinates of both horseshoes. Their
resolution-complex rows are short exact in every original degree.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be abelian and L a natural-number-indexed chain complex. A Cartan–Eilenberg resolution
specifies projective resolutions PBⱼ of outgoing boundaries and PHⱼ of homology. For each j, a
horseshoe resolves Zⱼ(L) from PBⱼ₊₁ and PHⱼ, and a second horseshoe resolves Lⱼ from that same
cycles resolution and PBⱼ. The chosen biproduct coordinates are part of this data. -/
structure CartanEilenbergResolution (L : ChainComplex C ℕ) where
  /-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L.
  Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For each j ∈ ℕ, boundaryResolution(j) is the specified projective resolution PBⱼ of Bⱼ⁽out⁾,
including the degree-zero outgoing boundary object. -/
  boundaryResolution (j : ℕ) : ProjectiveResolution (L.boundaryFrom j)
  /-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L.
  Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For each j ∈ ℕ, homologyResolution(j) is the specified projective resolution PHⱼ of Hⱼ(L). -/
  homologyResolution (j : ℕ) : ProjectiveResolution (L.homology j)
  /-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L.
  Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For each j, the cycle horseshoe is the projective-resolution extension for 0 → Bⱼ₊₁⁽out⁾ → Zⱼ(L)
→ Hⱼ(L) → 0, with specified endpoint resolutions PBⱼ₊₁ and PHⱼ. -/
  cyclesHorseshoe (j : ℕ) :
    ProjectiveResolution.HorseshoeData
      (L.boundaryCyclesHomologyShortExact j)
      (boundaryResolution (j + 1)) (homologyResolution j)
  /-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L.
  Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
The cycle specification identifies each resolution-degree-a cycle term PCⱼ,ₐ with PBⱼ₊₁,ₐ ⊕
PHⱼ,ₐ, compatibly with the horseshoe inclusion and projection. -/
  cyclesSpec (j : ℕ) : (cyclesHorseshoe j).Spec
  /-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L.
  Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For each j, the term horseshoe is the projective-resolution extension for 0 → Zⱼ(L) → Lⱼ →
Bⱼ⁽out⁾ → 0. Its left endpoint is the exact cycle resolution PCⱼ already chosen by the first
horseshoe, and its right endpoint is PBⱼ. -/
  termHorseshoe (j : ℕ) :
    ProjectiveResolution.HorseshoeData
      (L.cyclesTermBoundaryShortExact j)
      (cyclesHorseshoe j).middle (boundaryResolution j)
  /-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L.
  Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
The term specification identifies each resolution-degree-a term PTⱼ,ₐ with PCⱼ,ₐ ⊕ PBⱼ,ₐ,
compatibly with its horseshoe inclusion and projection. -/
  termSpec (j : ℕ) : (termHorseshoe j).Spec

namespace CartanEilenbergResolution

variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L. Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For every j, cyclesResolution(j) is the middle projective resolution PCⱼ of the
boundary–cycle–homology horseshoe. -/
abbrev cyclesResolution (j : ℕ) : ProjectiveResolution (L.cycles j) :=
  (P.cyclesHorseshoe j).middle

/-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L. Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For every j, termResolution(j) is the middle projective resolution PTⱼ of the
cycles–term–outgoing-boundary horseshoe. -/
abbrev termResolution (j : ℕ) : ProjectiveResolution (L.X j) :=
  (P.termHorseshoe j).middle

/-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L. Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For every original degree j, the chain complexes of PBⱼ₊₁, PCⱼ and PHⱼ form the horseshoe short
complex PBⱼ₊₁ → PCⱼ → PHⱼ, indexed internally by resolution degree. -/
abbrev cyclesShortComplex (j : ℕ) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk
    (P.cyclesHorseshoe j).i
    (P.cyclesHorseshoe j).p
    (P.cyclesHorseshoe j).zero

/-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L. Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For every original degree j, the chain complexes of PCⱼ, PTⱼ and PBⱼ form the horseshoe short
complex PCⱼ → PTⱼ → PBⱼ in resolution degree. -/
abbrev termShortComplex (j : ℕ) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk
    (P.termHorseshoe j).i
    (P.termHorseshoe j).p
    (P.termHorseshoe j).zero

/-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L. Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For every j ∈ ℕ, the horseshoe row 0 → PBⱼ₊₁.complex → PCⱼ.complex → PHⱼ.complex → 0 is short
exact in the category of nonnegative chain complexes. -/
theorem cyclesShortExact (j : ℕ) :
    (P.cyclesShortComplex j).ShortExact :=
  (P.cyclesHorseshoe j).shortExact

/-- Let C be abelian, L a chain complex indexed by ℕ, and P a Cartan–Eilenberg resolution of L. Its
boundary resolutions PBⱼ resolve the outgoing images Bⱼ⁽out⁾, its homology resolutions PHⱼ
resolve Hⱼ(L), its cycle resolutions PCⱼ resolve Zⱼ(L), and its term resolutions PTⱼ resolve Lⱼ.
For every j ∈ ℕ, the horseshoe row 0 → PCⱼ.complex → PTⱼ.complex → PBⱼ.complex → 0 is short
exact in the category of nonnegative chain complexes. -/
theorem termShortExact (j : ℕ) :
    (P.termShortComplex j).ShortExact :=
  (P.termHorseshoe j).shortExact

/-- Let C be abelian and L a nonnegative chain complex. Given explicit projective resolutions PBⱼ of
every outgoing boundary Bⱼ⁽out⁾ and PHⱼ of every Hⱼ(L), the two horseshoe constructions produce
Cartan–Eilenberg resolution data. The second horseshoe uses the cycles resolution already
produced by the first as its left endpoint. -/
noncomputable def ofResolutions (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) :
    CartanEilenbergResolution L := by
  let HC (j : ℕ) :
      Σ H : ProjectiveResolution.HorseshoeData
          (L.boundaryCyclesHomologyShortExact j) (PB (j + 1)) (PH j),
        H.Spec :=
    (ProjectiveResolution.horseshoe_spec_nonempty
      (L.boundaryCyclesHomologyShortExact j) (PB (j + 1)) (PH j)).some
  let HT (j : ℕ) :
      Σ H : ProjectiveResolution.HorseshoeData
          (L.cyclesTermBoundaryShortExact j) (HC j).1.middle (PB j),
        H.Spec :=
    (ProjectiveResolution.horseshoe_spec_nonempty
      (L.cyclesTermBoundaryShortExact j) (HC j).1.middle (PB j)).some
  exact
    { boundaryResolution := PB
      homologyResolution := PH
      cyclesHorseshoe := fun j => (HC j).1
      cyclesSpec := fun j => (HC j).2
      termHorseshoe := fun j => (HT j).1
      termSpec := fun j => (HT j).2 }

@[simp]
theorem ofResolutions_boundaryResolution (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) (j : ℕ) :
    (ofResolutions L PB PH).boundaryResolution j = PB j :=
  rfl

@[simp]
theorem ofResolutions_homologyResolution (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) (j : ℕ) :
    (ofResolutions L PB PH).homologyResolution j = PH j :=
  rfl

end CartanEilenbergResolution

end HomologicalComplex

end
