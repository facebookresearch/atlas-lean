---
not_ready: true
---

# 2. The extra FLM symmetry

Starting from $H$, construct the additional FLM symmetry on the Griess
algebra and study the group it generates with $H$. The precise symmetry,
its order, and its formulas remain source-audit tasks. No presentation or
list of construction-specific relations is invented here.

## Intended results

- Define the extra symmetry $s$ from the source. Prove invertibility and
  preservation of the Griess product and form used in the construction.
- Fix the ambient algebra-automorphism group and define
  $G=\langle H,s\rangle$, with explicit inclusions and source correspondence.
- Prove the source-required conjugation formulas, relations, and intersections
  of subgroups and conjugates, with their ambient groups specified.
- Establish centralizer and normalizer descriptions actually used by the
  finiteness and simplicity arguments. Do not assume $s$ normalizes all of
  $H$.

A centralizer consists of transformations commuting with a specified element
or subgroup. A normalizer preserves a subgroup under conjugation. Their
construction-specific descriptions need proofs, not definitions assuming the
desired subgroup equalities.

## External VOA interface

Generator lifts are a separate workstream. Each lift must fix the vacuum and
conformal vector and preserve every VOA mode product, including twisted-sector
products. Preserving the Griess product does not establish existence of a lift.

If the external workstream proves generation by weight two, restriction to
weight two is injective on VOA automorphisms. Once lifts exist, injectivity
transfers every relation on $B$ to the lifts. Record both generation and
lift existence as checked prerequisites of the eventual VOA embedding.

## Completion criterion

The symmetry, generated group, and all interactions needed by the audited
global proof must have checked definitions and proofs. Sample-vector checks
or verification of selected relations do not establish the entire milestone.

## Source questions

- Locate the exact transformation and its algebra-preservation argument.
- Identify the conjugated subgroups, intersections, and relations used later.
- Separate centralizer/normalizer results proved here from facts that would
  assume an already identified Monster.
- Record any VOA facts needed for the finite-group argument as external inputs.

## Depends on

- [The local subgroup](../local-subgroup/README.md)

## Sources

- [FLM passage checklist](../../sources/flm.md)
- [Project-authored scope](../../sources/scope.md)
