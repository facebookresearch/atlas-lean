/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fields of values of odd-degree characters (Oberwolfach Reports 9/2020)

Oberwolfach mini-workshop Kronecker, Plethysm, and Sylow Branching Coefficients and their
Applications to Complexity Theory (2020), G. Navarro: which fields occur as `ℚ(χ)` for odd-degree
irreducible complex characters `χ` of finite groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RepresentationTheory.Character

@[expose] public section

namespace MathlibExt.GroupTheory.OddDegreeCharacterFieldsOWR17472Problem006Wanted

/-!
Source: G. Navarro, in Mini-Workshop: Kronecker, Plethysm, and Sylow Branching Coefficients and
their Applications to Complexity Theory, Oberwolfach Reports 17 (2020), no. 9, pp. 526-527, DOI
10.4171/OWR/2020/09. UnsolvedMath record UM-30004416 (`OWR-17472-006`), dataset ulamai/UnsolvedMath
v1.8.0.

Fields are subfields of `ℂ`. `ℚ(χ)` is generated over `ℚ` by the values of the character of an
irreducible (simple) finite-dimensional complex representation; odd degree is odd dimension. `F/ℚ`
abelian is read as `F ⊆ ℚ(ζ_f)` for some `f ≥ 1` (Kronecker-Weber), and the conductor of `F` is the
least such `f`, as in the source.
-/

/-- The cyclotomic field `ℚ(ζ_f) ⊆ ℂ` with `ζ_f = e^{2πi/f}`. -/
noncomputable def cyclotomicSubfield (f : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / f)}

/-- The conductor of an abelian number field `F ⊆ ℂ`: the least `f ≥ 1` with `F ⊆ ℚ(ζ_f)`. -/
noncomputable def conductor (F : IntermediateField ℚ ℂ) : ℕ :=
  sInf {f : ℕ | 0 < f ∧ F ≤ cyclotomicSubfield f}

/-- The field of values `ℚ(χ) ⊆ ℂ` of the character `χ` of a complex representation `V`. -/
noncomputable def characterField {G : Type} [Group G] (V : FDRep ℂ G) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range V.character)

/-- Navarro's question (Oberwolfach Report 9/2020, p. 526), answered: a subfield `F ⊆ ℂ` is the
field of values `ℚ(χ)` of an odd-degree irreducible complex character `χ` of some finite group if
and only if `F/ℚ` is abelian (`F ⊆ ℚ(ζ_f)` for some `f ≥ 1`) and `ℚ(ζ_{2^a}) ⊆ F`, where `2^a` is
the `2`-part of the conductor of `F`. -/
def oddDegreeCharacterFields : Prop :=
  ∀ F : IntermediateField ℚ ℂ,
    (∃ (G : Type) (_ : Group G) (_ : Finite G) (V : FDRep ℂ G), CategoryTheory.Simple V ∧
        Odd (Module.finrank ℂ V) ∧ F = characterField V) ↔
      ((∃ f : ℕ, 0 < f ∧ F ≤ cyclotomicSubfield f) ∧
        cyclotomicSubfield (2 ^ (conductor F).factorization 2) ≤ F)

/--
Resolved true: Navarro and Tiep proved that the field of values of an odd-degree irreducible
character with conductor `2^a m` (`m` odd) contains `ℚ(ζ_{2^a})` (Theorem A1) and that every abelian
`F/ℚ` with this property is such a field (Theorem A2), so these fields are exactly the abelian `F`
with `ℚ(ζ_{2^a}) ⊆ F`, `2^a` the 2-part of the conductor. Source: G. Navarro, in Mini-Workshop:
Kronecker, Plethysm, and Sylow Branching Coefficients and their Applications to Complexity Theory,
Oberwolfach Reports 17 (2020), no. 9, pp. 526-527, DOI 10.4171/OWR/2020/09; resolution: G. Navarro
and P. H. Tiep, The fields of values of characters of degree not divisible by p, Forum Math. Pi 9
(2021), e2, Theorem A1: if χ ∈ Irr(G) has odd degree and conductor 2^a m with m odd, then ℚ_{2^a} ⊆
ℚ(χ); Theorem A2: every abelian F/ℚ with conductor 2^a m (m odd) and ℚ_{2^a} ⊆ F is ℚ(χ) for an
odd-degree χ of some finite group; the source states the answer on p. 527,
https://doi.org/10.1017/fmp.2021.1.
-/
public theorem_wanted oddDegreeCharacterFields_holds : oddDegreeCharacterFields

end MathlibExt.GroupTheory.OddDegreeCharacterFieldsOWR17472Problem006Wanted
