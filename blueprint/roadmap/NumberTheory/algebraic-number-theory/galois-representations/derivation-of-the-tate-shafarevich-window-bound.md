# Derivation of the Tate–Shafarevich window bound from automorphic Galois representations

This node is still to be broken down. It covers a conditional derivation: if the
[Galois representations attached to polarized regular algebraic cuspidal representations over CM fields](galois-representations-attached-to-polarized-cuspidal-representations.md)
exist with the properties stated there, then the
[window bound for Tate–Shafarevich groups of Tate twists over subfields of cyclotomic fields](tate-shafarevich-window-bound-over-cyclotomic-subfields.md)
holds, given base change for $\mathrm{GL}_n$ and the published results listed below. The window
bound itself takes both the Galois representations and this derivation as its proof inputs. The
argument is long, and its intermediate statements are formulated with notions specific to this proof;
they are not yet stated as pages because each needs those notions stated and checked first.

The published results that the argument consumes are:

- on representations of $\mathrm{GL}_n$ over $p$-adic fields: the finiteness and geometric lemma of
  Bernstein and Zelevinsky, Bernstein's irreducibility of products of unitary representations,
  Zelevinsky's classification with the polynomial structure of the Grothendieck ring, the
  irreducibility of products of representations whose cuspidal supports are totally disjoint, the
  essentially square-integrable representations as those attached to segments, the generic
  representations as products over pairwise unlinked segments, tempered representations as
  products of square-integrable ones, the Langlands classification with its standard modules, the
  local converse theorem, and the depth zero of representations whose cuspidal supports have depth
  zero;
- on automorphic forms on $\mathrm{GL}_n$: the finiteness of spaces of automorphic forms, the
  classification of Jacquet and Shalika, base change to isobaric representations, the theorem of
  Gelfand and Kazhdan, and Clozel's results on cohomological representations;
- on global fields: global Artin reciprocity, the $\ell$-adic Galois characters attached to algebraic
  Hecke characters (their existence and their Weil–Deligne representations at the places above
  $\ell$), and Berger's theorem that de Rham representations are potentially semistable;
- on cyclotomic fields: the theorem of Ferrero and Washington, that for a prime $\ell$ and an abelian
  number field $K$ containing the $\ell$-th roots of unity ($4$-th roots if $\ell = 2$) the
  $\ell$-ranks of the class groups of the fields $K(\mu_{\ell^n})$, $n \ge 0$, are bounded (the
  vanishing of the Iwasawa $\mu$-invariant);
- on Galois cohomology: Poitou–Tate duality, the finiteness of local cohomology and local Tate
  duality over finite extensions of $\mathbb{Q}_\ell$, the orthogonality of unramified classes under
  local duality, and, for representations with rational coefficients, the Bloch–Kato dimension
  formula and the orthogonality of the Bloch–Kato subspaces under local duality;
- Brauer's induction theorem in degree zero and Chevalley's theorem on congruence units.

The bundles of published inputs that the library assembles for this argument contain further results
that no step of the argument uses, and the page lists none of them: Green's description of the
cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_p)$, the Jacquet modules of vectors fixed by principal
congruence subgroups, rapid decay of cusp forms, Harish-Chandra's finiteness theorem, the cuspidal
spectrum, Clozel's purity lemma, ray class fields, and the whole bundle on abelian varieties with
complex multiplication (Grothendieck–Messing theory, the de Rham cohomology of abelian schemes,
period comparison, Serre–Tate good reduction, the main theorem of complex multiplication, the
Hilbert class field, the theorems of Siegel–Klingen and Deligne–Ribet, and the functional equations
of partial zeta functions and of Hecke $L$-functions).

A good expansion has pages for the intermediate statements of the argument, in order, each with the
inputs above that it uses; pages for the inputs not yet in the vault, among them the theorem of
Ferrero and Washington, the $\ell$-adic Galois characters attached to algebraic Hecke characters,
Brauer's induction theorem in degree zero and Chevalley's theorem on congruence units; and, once the
node on Galois cohomology is broken down, links to its pages for the results on Galois cohomology
above only, with the definitions of Tate–Shafarevich groups, twists and restricted Galois groups
linked from the window bound.

## Depends on

- [Galois representations attached to polarized regular algebraic cuspidal representations over CM fields](galois-representations-attached-to-polarized-cuspidal-representations.md), whose statement is the hypothesis of the derivation

## Proof depends on

- [Smooth representations of p-adic GLₙ and the local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/smooth-representations-of-p-adic-gl-n-and-local-langlands.md), for the results on representations of $p$-adic $\mathrm{GL}_n$ listed above
- [Automorphic representations of GLₙ and unitary groups](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n-and-unitary-groups.md), for the results on automorphic forms on $\mathrm{GL}_n$ listed above, base change among them
- [Global Artin reciprocity](../adeles-class-field-theory/global-artin-reciprocity.md)
- [Galois cohomology and p-adic Hodge theory](../../galois-representations/galois-cohomology-and-p-adic-hodge-theory.md), for the results on Galois cohomology listed above and Berger's theorem

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it, with `AV/` for `src/Development/AutomorphicArithmetic/AutomorphicVarieties/` and `.../DenseThresholdCases/` for `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/`). The node is `UpperTheory.One.Join.automorphic_window_of_inputs` (`.../DenseThresholdCases/TopMainZj.lean`, lines 71–74), whose argument `gal` is the hypothesis: `UpperTheory.One.vwin_of_row` (`.../DenseThresholdCases/VwinOfRow.lean`, lines 4–5) applies it to the Galois representations `h` and to base change `UpperTheory.BaseChangeIdentities.baseChangeN`, and the window bound has these two proof inputs. The argument itself is `UpperTheory.V.v_window_of_literal_automorphy_n` (`.../DenseThresholdCases/WindowBoundOfLiteratureLevel.lean`, lines 22–34), through `UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt` (`.../DenseThresholdCases/PublishedHypothesesFromPatching.lean`, line 98, which stores the inputs as the field `litN`) and `vwin_of_hypotheses_H_E_alt`. The inputs are assembled in `TopMainZj.lean` as four bundles, the fields of `GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis` (`.../DenseThresholdCases/LitAut.lean`, lines 12–63): `local_inputs_from_literature` (lines 18–37), `automorphic_inputs_from_literature` (lines 38–54, with the Galois representations as `gal` at line 47 and base change as `bc` at line 45), `galois_cohomology_from_literature` (`.../DenseThresholdCases/TemperedProductOfSquareIntegrable.lean`, lines 331–343) and `cm_abelian_inputs_from_literature` (lines 59–70). A field counts here as consumed when some step projects it: the fields of the first two bundles listed above are projected under `AV/` (for example `.loc.bz` at `AV/AutomorphicForms/TemperedLocalComponents/LocFixed.lean`, line 77, `.loc.conv` at `AV/TheoremsMuLinked/GaloisRepresentationTypes/MapOfRep.lean`, line 26, `.aut.js` and `.aut.gk` at `AV/AutomorphicForms/TemperedLocalComponents/SelfDualC.lean`, line 122, `.aut.art` at `AV/HeckeAlgebras/UpOperatorEigenvalues/HeckeCoeff.lean`, line 58, `.aut.chA` and `.aut.berger` at `AV/PadicHodgeTheory/CharDR.lean`, line 47, `.aut.chW` at `AV/BuildingsResidueChars/CompatiblePolarizationOfLink.lean`, line 52, `.loc.brauer` at `AV/ModularityArgument/LinkedUnramifiedChains/TeichmullerParts/SubalgebraIntegrality/RadOfDense.lean`, line 21, and `.loc.chev` at `AV/HeckeAlgebras/OrdinaryHeckeCharacters/CoefIsCoef.lean`, line 33), while the fields `green`, `mp` and `sq` of the first bundle, `decay`, `hc`, `cusp`, `pur` and `ray` of the second, and the field `cm` of `LiteratureRankNHypothesis`, which holds the whole fourth bundle, are projected nowhere in the library. The results on Galois cohomology are consumed in the final step `UpperTheory.V.HV.Core.of_four_alt` (`.../DenseThresholdCases/HVCore.lean`, lines 18–22): Poitou–Tate duality (`UpperTheory.V.HV.U.pt_s`, from the field `pt`), local finiteness and local Tate duality over finite extensions (`coh.lfK`, `coh.ltK`), passed to `UpperTheory.V.Win.thmBab_of_lemmaK` (`AV/LayeredIsomorphisms/ThmBabOfLemmaK.lean`, lines 9–12) and `vwin_of_counts`, and the orthogonality of unramified classes (`coh.uo`, line 22); the Bloch–Kato dimension formula and the rational orthogonality are the components `.1` and `.2.1` of `BlochKatoLocal` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/RationalDualityOfAllCoefficients.lean`, lines 60–62) projected at `AV/PadicHodgeTheory/CocycleTransportH1fSurjective.lean`, line 142, and `AV/ModularityArgument/LinkedUnramifiedChains/CrystallineCardinalities/CupUnr.lean`, line 74. The theorem of Ferrero and Washington, `UpperTheory.V.Published.FerreroWashington` (`AV/PublishedTheorems/FerreroWashington.lean`, lines 7–11), proved as `UpperTheory.V.FW.ferreroWashington` (`AV/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`, line 104), is supplied at `.../DenseThresholdCases/Sp4In0.lean`, lines 18–19 (in `sp4In0_alt`, which `vwin_of_hypotheses_H_E_alt` uses at `WindowBoundOfLiteratureLevel.lean`, line 28) and at `HVCore.lean`, line 19. Brauer's and Chevalley's theorems are `GlobalTheory.Published.BrauerDegreeZero` and `GlobalTheory.Published.ChevalleyUnits` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BrauerDegreeZero.lean`, lines 12–17, and `ChevalleyUnits.lean`, lines 7–9).
