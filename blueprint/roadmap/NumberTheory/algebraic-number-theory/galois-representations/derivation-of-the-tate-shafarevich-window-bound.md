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
  Gelfand and Kazhdan (derived from the rigidity of Jacquet and Shalika and the boundedness of cusp
  forms, which comes from the description of the cuspidal spectrum), and Clozel's results on
  cohomological representations;
- on global fields: global Artin reciprocity, the $\ell$-adic Galois characters attached to algebraic
  Hecke characters (their existence, their de Rham property at the places above $\ell$ and their
  Weil–Deligne representations there), and Berger's theorem that de Rham representations are
  potentially semistable;
- on cyclotomic fields: the theorem of Ferrero and Washington, that for a prime $\ell$ and an abelian
  number field $K$ containing the $\ell$-th roots of unity ($4$-th roots if $\ell = 2$) the
  $\ell$-ranks of the class groups of the fields $K(\mu_{\ell^n})$, $n \ge 0$, are bounded (the
  vanishing of the Iwasawa $\mu$-invariant);
- on Galois cohomology, for finite Galois modules with coefficients $\mathbb{Z}/\ell^r$: the
  Poitou–Tate sequence and the duality of Tate–Shafarevich groups of a finite module and of its
  Cartier dual, for $\ell$ odd or a totally imaginary base field; the global finiteness theorem and
  the global Euler characteristic formula; the local finiteness theorem, local Tate duality and the
  local Euler characteristic formula, with local finiteness and local Tate duality also over finite
  extensions of $\mathbb{Q}_\ell$; the orthogonality of unramified classes under local duality; and the
  Greenberg–Wiles formula for Selmer groups. The counts of the argument apply the global formulas over $\mathbb{Q}$ and over
  totally real fields, for odd $\ell$, with the archimedean terms given by complex conjugations at the
  real places; the passage from these finite levels to the coefficients
  $\mathbb{Q}_\ell/\mathbb{Z}_\ell$ of the window bound is part of the argument. For representations
  with rational coefficients the argument also uses the Bloch–Kato dimension formula and the
  orthogonality of the Bloch–Kato subspaces under local duality;
- Brauer's induction theorem in degree zero and Chevalley's theorem on congruence units.

A good expansion has pages for the intermediate statements of the argument, in order, each with the
inputs above that it uses; pages for the inputs not yet in the vault, among them the theorem of
Ferrero and Washington, the $\ell$-adic Galois characters attached to algebraic Hecke characters,
Brauer's induction theorem in degree zero and Chevalley's theorem on congruence units. The results
on Galois cohomology above are linked below to the pages of their own expansion, and the definitions
of Tate–Shafarevich groups, Tate twists and Galois groups with restricted ramification are linked
from the window bound.

## Depends on

- [Galois representations attached to polarized regular algebraic cuspidal representations over CM fields](galois-representations-attached-to-polarized-cuspidal-representations.md), whose statement is the hypothesis of the derivation

## Proof depends on

- [Finite length of parabolically induced representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md), for the finiteness theorem of Bernstein and Zelevinsky
- [The Bernstein–Zelevinsky geometric lemma](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/bernstein-zelevinsky-geometric-lemma.md)
- [Zelevinsky's classification of the irreducible representations of GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/zelevinsky-classification.md), for the classification with the polynomial structure of the Grothendieck ring and the irreducibility of products of segments no two of which are linked, products with totally disjoint cuspidal supports among them
- [Essentially square-integrable representations of GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/essentially-square-integrable-representations-of-gl-n.md), for the essentially square-integrable representations as those attached to segments
- [Tempered and unitary representations of GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/tempered-and-unitary-representations-of-gl-n.md), for Bernstein's irreducibility of products of unitary representations and the tempered representations as products of square-integrable ones
- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for the generic representations as products over pairwise unlinked segments
- [Langlands classification for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), with its standard modules
- [Local converse theorem for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/local-converse-theorem-for-gl-n.md)
- [Depth under parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/depth-under-parabolic-induction-and-jacquet-functors.md), for the depth zero of representations whose cuspidal supports have depth zero
- [Harish-Chandra's finiteness theorem for automorphic forms](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/harish-chandra-finiteness-theorem.md), for the finiteness of spaces of automorphic forms
- [Jacquet–Shalika classification of automorphic representations of GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/jacquet-shalika-classification.md), for the classification of Jacquet and Shalika and its rigidity
- [Discreteness of the cuspidal spectrum](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md), for the description of the cuspidal spectrum, which gives the boundedness of cusp forms from which, with the rigidity, the input of Gelfand and Kazhdan is derived
- [Base change and automorphic induction for GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/base-change-and-automorphic-induction-for-gl-n.md), for base change to isobaric representations
- [Algebraic automorphic representations and Clozel's purity lemma](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/algebraic-automorphic-representations-and-clozel-purity.md), for Clozel's results on cohomological representations
- [Global reciprocity law](../adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the global Artin map
- [Poitou–Tate exact sequence](galois-cohomology-of-number-fields/poitou-tate-exact-sequence.md), at finite level, with the lifting of local $2$-cocycles that a count derives from it
- [Poitou–Tate duality](galois-cohomology-of-number-fields/poitou-tate-duality.md), for the duality of Tate–Shafarevich groups at finite level, for $\ell$ odd or a totally imaginary field
- [Finiteness and cohomological dimension of Galois groups with restricted ramification](galois-cohomology-of-number-fields/finiteness-and-cohomological-dimension-of-g-s.md), for global finiteness
- [Global Euler characteristic formula](galois-cohomology-of-number-fields/global-euler-characteristic-formula.md), over $\mathbb{Q}$ and totally real fields, for odd $\ell$
- [Wiles's formula for Selmer groups](galois-cohomology-of-number-fields/greenberg-wiles-formula.md), over totally real fields, for odd $\ell$
- [Cohomological dimension and finiteness for p-adic fields](galois-cohomology-of-local-fields/cohomological-dimension-of-p-adic-fields.md), for local finiteness, also over finite extensions of $\mathbb{Q}_\ell$
- [Local Tate duality](galois-cohomology-of-local-fields/local-tate-duality.md), also over finite extensions of $\mathbb{Q}_\ell$
- [Galois cohomology of Tate twists over a p-adic field](galois-cohomology-of-local-fields/cohomology-of-tate-twists-over-p-adic-fields.md), for the duality between $H^2(\mathbb{Z}_\ell(e + 1))$ and $H^0(\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e))$ at the places above $\ell$, in the passage to the coefficients $\mathbb{Q}_\ell/\mathbb{Z}_\ell$
- [Local Euler characteristic formula](galois-cohomology-of-local-fields/local-euler-characteristic-formula.md)
- [Unramified classes under local duality](galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the orthogonality of unramified classes
- [Bloch–Kato dimension formula](p-adic-hodge-theory/bloch-kato-dimension-formula.md), for representations with rational coefficients
- [Bloch–Kato orthogonality](p-adic-hodge-theory/bloch-kato-orthogonality.md), for representations with rational coefficients
- [p-adic monodromy theorem](p-adic-hodge-theory/p-adic-monodromy-theorem.md), for Berger's theorem that de Rham representations are potentially semistable

## Sources

- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, cited by paths in it, with `AV/` for `src/Development/AutomorphicArithmetic/AutomorphicVarieties/` and `.../DenseThresholdCases/` for `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/`). The node is `UpperTheory.One.Join.automorphic_window_of_inputs` (`.../DenseThresholdCases/TopMainZj.lean`, lines 71–74), whose argument `gal` is the hypothesis: `UpperTheory.One.vwin_of_row` (`.../DenseThresholdCases/VwinOfRow.lean`, lines 4–5) applies it to the Galois representations `h` and to base change `UpperTheory.BaseChangeIdentities.baseChangeN`, and the window bound has these two proof inputs. The argument itself is `UpperTheory.V.v_window_of_literal_automorphy_n` (`.../DenseThresholdCases/WindowBoundOfLiteratureLevel.lean`, lines 22–34), through `UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt` (`.../DenseThresholdCases/PublishedHypothesesFromPatching.lean`, line 98, which stores the inputs as the field `litN`) and `vwin_of_hypotheses_H_E_alt`. The inputs are assembled in `TopMainZj.lean` as four bundles, the fields of `GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis` (`.../DenseThresholdCases/LitAut.lean`, lines 12–63): `local_inputs_from_literature` (lines 18–37), `automorphic_inputs_from_literature` (lines 38–54, with the Galois representations as `gal` at line 47 and base change as `bc` at line 45), `galois_cohomology_from_literature` (`.../DenseThresholdCases/TemperedProductOfSquareIntegrable.lean`, lines 331–343) and `cm_abelian_inputs_from_literature` (lines 59–70). A field counts here as consumed when some step projects it. The fields of the first two bundles listed above are projected under `AV/` (for example `.loc.bz` at `AV/AutomorphicForms/TemperedLocalComponents/LocFixed.lean`, line 77, `.loc.conv` at `AV/TheoremsMuLinked/GaloisRepresentationTypes/MapOfRep.lean`, line 26, `.aut.js` and `.aut.gk` at `AV/AutomorphicForms/TemperedLocalComponents/SelfDualC.lean`, line 122, `.aut.art` at `AV/HeckeAlgebras/UpOperatorEigenvalues/HeckeCoeff.lean`, line 58, `.aut.chW` at `AV/BuildingsResidueChars/CompatiblePolarizationOfLink.lean`, line 52, `.loc.brauer` at `AV/ModularityArgument/LinkedUnramifiedChains/TeichmullerParts/SubalgebraIntegrality/RadOfDense.lean`, line 21, and `.loc.chev` at `AV/HeckeAlgebras/OrdinaryHeckeCharacters/CoefIsCoef.lean`, line 33). The de Rham property of the $\ell$-adic characters of algebraic Hecke characters is `dr_of_above N.aut.chA`, used with `N.aut.berger` and `N.aut.chW` in `UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l` (`.../DenseThresholdCases/LocCharDR.lean`, lines 35–46). The cuspidal spectrum enters through the Gelfand–Kazhdan field: `gelfand_kazhdan_dual_of_open` derives it from the rigidity of Jacquet and Shalika and from the boundedness of cusp forms `UpperTheory.V.Af.cuspSpectrumGL.2.2` (`TemperedProductOfSquareIntegrable.lean`, lines 245–250), and `bc_regAlg_polarizedPair_alt` uses it (`.../DenseThresholdCases/BcRegAlgPolarizedPair.lean`, lines 13–19). On this route the separate fields `green`, `mp` and `sq` of the first bundle, `decay`, `hc`, `cusp`, `pur` and `ray` of the second, and `cm` of `LiteratureRankNHypothesis`, which holds the fourth bundle, are not projected, so the page has no direct arrow for them; this says nothing about uses of the corresponding theorems elsewhere in the proof, such as the cuspidal spectrum above. The results on Galois cohomology are consumed as follows. The count `CountV` applies `hostFrame_count` to local finiteness, local Tate duality, the local Euler characteristic, global finiteness, the global Euler characteristic and the Poitou–Tate statement (`.../DenseThresholdCases/CountVOf.lean`, lines 48–51), and `AV/UnitaryThreeDeformations/HostCount.lean`, lines 348–351, applies the global Euler characteristic formula over $\mathbb{Q}$ for odd $\ell$, with a complex conjugation at the real place (line 348), the local formulas at each place of $S$ (lines 349–350), and, at line 351, `UpperTheory.global_cohomology_finite_set` (`AV/UnitaryThreeDeformations/GlobalCohomologyFiniteSet.lean`, lines 34–41), which derives from the normalized Poitou–Tate statement that prescribed local $2$-cocycles at the places of $S$ lift, modulo coboundaries, to a global $2$-cocycle when some element acts by a scalar different from the value of the cyclotomic character modulo $\ell$. The count `CountI` reaches, through `linkedUnlE_alt` (`.../DenseThresholdCases/LinkedUnlE.lean`, lines 46–53) and `tanA_of` (`AV/ModularityArgument/LinkedUnramifiedChains/CrystallineCardinalities/TanAOf.lean`, line 36), the evaluation of global finiteness twice and of the Greenberg–Wiles formula, over totally real fields for $\ell \ne 2$ with the archimedean terms at the real places (`AV/ModularityArgument/LinkedUnramifiedChains/CrystallineCardinalities/FiniteCocyclesOfFiniteH1.lean`, lines 224–225 and 240–249). The Poitou–Tate statement `GlobalTheory.Published.PoitouTateDuality` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean`, lines 13–27: the nine-term sequence and the duality `ShaDual` for finite modules, for $\ell \ne 2$ or a totally imaginary field) is applied at each finite level by `GlobalTheory.TateLimit.finite_level` (`src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LengthEqLengthInvariantsOfTorsionLevels.lean`, lines 517–525), and the passage from the finite levels to the coefficients $\mathbb{Q}_\ell/\mathbb{Z}_\ell$ is `vFormula_of_classicalTheorems` (`AV/GaloisLibrary/GaloisCohomologyLength/Formula.lean`, lines 15–24), with local finiteness and local Tate duality over finite extensions; it is also consumed in the final step `UpperTheory.V.HV.Core.of_four_alt` (`.../DenseThresholdCases/HVCore.lean`, lines 18–22) as `UpperTheory.V.HV.U.pt_s`, with local finiteness and local Tate duality over finite extensions (`coh.lfK`, `coh.ltK`), passed to `UpperTheory.V.Win.thmBab_of_lemmaK` (`AV/LayeredIsomorphisms/ThmBabOfLemmaK.lean`, lines 9–12) and `vwin_of_counts`, and the orthogonality of unramified classes (`coh.uo`, line 22); the Bloch–Kato dimension formula and the rational orthogonality are the components `.1` and `.2.1` of `BlochKatoLocal` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/RationalDualityOfAllCoefficients.lean`, lines 60–62) projected at `AV/PadicHodgeTheory/CocycleTransportH1fSurjective.lean`, line 142, and `AV/ModularityArgument/LinkedUnramifiedChains/CrystallineCardinalities/CupUnr.lean`, line 74. The theorem of Ferrero and Washington, `UpperTheory.V.Published.FerreroWashington` (`AV/PublishedTheorems/FerreroWashington.lean`, lines 7–11), proved as `UpperTheory.V.FW.ferreroWashington` (`AV/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`, line 104), is supplied at `.../DenseThresholdCases/Sp4In0.lean`, lines 18–19 (in `sp4In0_alt`, which `vwin_of_hypotheses_H_E_alt` uses at `WindowBoundOfLiteratureLevel.lean`, line 28) and at `HVCore.lean`, line 19. Brauer's and Chevalley's theorems are `GlobalTheory.Published.BrauerDegreeZero` and `GlobalTheory.Published.ChevalleyUnits` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BrauerDegreeZero.lean`, lines 12–17, and `ChevalleyUnits.lean`, lines 7–9).
