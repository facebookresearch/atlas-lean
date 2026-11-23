# Derivation of the Tate–Shafarevich window bound from automorphic Galois representations

This node is still to be broken down. It covers the argument that derives the
[window bound for Tate–Shafarevich groups of Tate twists over subfields of cyclotomic fields](tate-shafarevich-window-bound-over-cyclotomic-subfields.md)
from the
[Galois representations attached to polarized regular algebraic cuspidal representations over CM fields](galois-representations-attached-to-polarized-cuspidal-representations.md),
with base change for $\mathrm{GL}_n$ and the published results listed below. The argument is long,
and its intermediate statements are formulated with notions specific to this proof; they are not
yet stated as pages because each needs those notions stated and checked first.

The published results that the argument takes as inputs are:

- on representations of $\mathrm{GL}_n$ over $p$-adic fields: the finiteness and geometric lemma of
  Bernstein and Zelevinsky, Bernstein's irreducibility of products of unitary representations,
  Zelevinsky's classification with the polynomial structure of the Grothendieck ring, the
  irreducibility of products of representations whose cuspidal supports are totally disjoint, the
  essentially square-integrable representations as those attached to segments, the generic
  representations as products over pairwise unlinked segments, the Jacquet modules of vectors fixed
  by principal congruence subgroups (Moy–Prasad), tempered representations as products of
  square-integrable ones, the Langlands classification with its standard modules, the local
  converse theorem, the depth zero of representations whose cuspidal supports have depth zero, and
  Green's description of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_p)$;
- on automorphic forms on $\mathrm{GL}_n$: rapid decay of cusp forms, Harish-Chandra's finiteness
  theorem, the finiteness of spaces of automorphic forms, the classification of Jacquet and
  Shalika, the cuspidal spectrum, base change to isobaric representations, the theorem of Gelfand
  and Kazhdan, and Clozel's purity lemma with his results on cohomological representations;
- on global fields: global Artin reciprocity, ray class fields, the $\ell$-adic Galois characters
  attached to algebraic Hecke characters (their existence, their de Rham property, and their
  Weil–Deligne representations at the places above $\ell$), and Berger's theorem that de Rham
  representations are potentially semistable;
- on cyclotomic fields: the theorem of Ferrero and Washington, that for a prime $\ell$ and an abelian
  number field $K$ containing the $\ell$-th roots of unity ($4$-th roots if $\ell = 2$) the
  $\ell$-ranks of the class groups of the fields $K(\mu_{\ell^n})$, $n \ge 0$, are bounded (the
  vanishing of the Iwasawa $\mu$-invariant);
- on Galois cohomology: the Poitou–Tate sequence, local and global finiteness, local Tate duality,
  the local and global Euler characteristic formulas, the orthogonality of unramified classes,
  Wiles's formula for Selmer groups (in Greenberg's form), and the Bloch–Kato dimension formula;
- on abelian varieties with complex multiplication: Grothendieck–Messing deformation theory, the de
  Rham cohomology of abelian schemes and its duality, period comparison and the Gauss–Manin
  connection, the good reduction of CM abelian varieties (Serre–Tate), the main theorem of complex
  multiplication, the generation of Hilbert class fields by $j$-invariants, the theorem of Siegel and
  Klingen with the $p$-adic interpolation of Deligne and Ribet, and the functional equations of
  partial zeta functions and of Hecke $L$-functions.

A good expansion has pages for the intermediate statements of the argument, in order, each with the
inputs above that it uses; pages for the inputs not yet in the vault, among them the theorem of
Ferrero and Washington, the $\ell$-adic Galois characters attached to algebraic Hecke characters,
the theorems of Siegel–Klingen and Deligne–Ribet, period comparison and the Gauss–Manin connection
for abelian schemes, Brauer's induction theorem in degree zero and Chevalley's theorem on congruence
units, which the inputs also contain; and links to the pages that the nodes below break down.

## Proof depends on

- [Smooth representations of p-adic GLₙ and the local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/smooth-representations-of-p-adic-gl-n-and-local-langlands.md), for the results on representations of $p$-adic $\mathrm{GL}_n$ listed above
- [Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$](../../../GroupTheory/characters-of-finite-groups/green-cuspidal-characters-of-gl-n.md), for the case of a prime field
- [Automorphic representations of GLₙ and unitary groups](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n-and-unitary-groups.md), for the results on automorphic forms on $\mathrm{GL}_n$ listed above, base change among them
- [Global Artin reciprocity](../adeles-class-field-theory/global-artin-reciprocity.md)
- [Existence theorem of global class field theory](../adeles-class-field-theory/global-existence-theorem.md), for the ray class fields
- [Galois cohomology and p-adic Hodge theory](../../galois-representations/galois-cohomology-and-p-adic-hodge-theory.md), for the results on Galois cohomology listed above and Berger's theorem
- [Abelian schemes and their moduli](../../../AlgebraicGeometry/abelian-varieties/abelian-schemes-and-their-moduli.md), for Grothendieck–Messing deformation theory, the cohomology of abelian schemes and the good reduction of CM abelian varieties
- [Main theorem of complex multiplication for elliptic curves](../adeles-class-field-theory/hilbert-class-field/main-theorem-of-complex-multiplication.md)
- [The j-invariant of a CM lattice generates the Hilbert class field](../adeles-class-field-theory/hilbert-class-field/hilbert-class-field-generated-by-j.md)
- [Functional equation of Hecke L-functions](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-functional-equation.md), for the functional equations of Hecke $L$-functions and of partial zeta functions

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it, with `.../DenseThresholdCases/` for `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/`). The node is `UpperTheory.One.Join.automorphic_window_of_inputs` (`.../DenseThresholdCases/TopMainZj.lean`, lines 71–74), which `UpperTheory.One.vwin_of_row` applies (`.../DenseThresholdCases/VwinOfRow.lean`, lines 4–5). The argument itself is `UpperTheory.V.v_window_of_literal_automorphy_n` (`.../DenseThresholdCases/WindowBoundOfLiteratureLevel.lean`, lines 22–34), through `UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt` and `vwin_of_hypotheses_H_E_alt`, whose steps the library names after patching, counting, and descent and vanishing reductions. The inputs are consumed in `TopMainZj.lean` as the fields of four bundles: the results on representations of $p$-adic $\mathrm{GL}_n$, Brauer's theorem and Chevalley's theorem at lines 20–36 (`local_inputs_from_literature`), Green's description at line 37; the results on automorphic forms at lines 40–44, 46 and 48–49 (`automorphic_inputs_from_literature`), with base change at line 45, supplied by `UpperTheory.BaseChangeIdentities.baseChangeN` at `VwinOfRow.lean`, line 5, and the Galois representations at line 47; global Artin reciprocity at line 50, the ray class fields at line 51, the $\ell$-adic characters of algebraic Hecke characters at lines 52–53 and Berger's theorem at line 54; the results on Galois cohomology through `UpperTheory.LiteratureTheorems.galois_cohomology_from_literature` (`.../DenseThresholdCases/TemperedProductOfSquareIntegrable.lean`, lines 331–343) at line 58; and the results on abelian varieties with complex multiplication at lines 60–70 (`cm_abelian_inputs_from_literature`): Grothendieck–Messing deformation theory at line 60, the de Rham cohomology of abelian schemes and its duality at lines 61–62, period comparison and the Gauss–Manin connection at lines 63–64, Serre–Tate good reduction at line 65, the main theorem of complex multiplication at line 66, the Hilbert class field at line 67, Siegel–Klingen and Deligne–Ribet at line 68, and the functional equations of partial zeta functions and of Hecke $L$-functions at lines 69–70. The theorem of Ferrero and Washington, `UpperTheory.V.Published.FerreroWashington` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean`, lines 7–11), proved as `UpperTheory.V.FW.ferreroWashington` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`, line 104), is consumed at `.../DenseThresholdCases/Sp4In0.lean`, line 19, in `sp4In0_alt`, which `vwin_of_hypotheses_H_E_alt` uses at `WindowBoundOfLiteratureLevel.lean`, line 28. The library proves the bundled inputs in `TemperedProductOfSquareIntegrable.lean`, lines 207–344, among them `GlobalTheory.Published.BrauerDegreeZero` and `GlobalTheory.Published.ChevalleyUnits` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BrauerDegreeZero.lean`, lines 12–17, and `ChevalleyUnits.lean`, lines 7–9).
