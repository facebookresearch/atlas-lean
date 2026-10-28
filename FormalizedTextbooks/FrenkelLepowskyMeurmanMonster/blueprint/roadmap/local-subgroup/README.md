---
not_ready: true
---

# 1. The local subgroup

Construct a concrete $H$ of intended shape
$2_+^{1+24}\!\cdot\mathrm{Co}_1$ with a faithful action on the FLM Griess
algebra $B$. The source formulas and proof dependencies remain to be checked.

## Intended results

- Construct the extraspecial group $Q$ of order $2^{25}$. Prove that
  its center has order two, identify $Q/Z(Q)$ with the additive group of
  $\mathbb F_2^{24}$, and establish the plus-type quadratic-form property.
- Construct the Leech lattice and lattice-symmetry facts used by FLM.
  Define $\mathrm{Co}_0$ as its isometry group and
  $\mathrm{Co}_1=\mathrm{Co}_0/\{\pm1\}$. Trace the actual Golay-code
  construction and Conway-group properties needed by the source proof.
- Construct the specific FLM extension

  $$
  1\longrightarrow Q\longrightarrow H\longrightarrow\mathrm{Co}_1
  \longrightarrow1.
  $$

  Prove injectivity, surjectivity, and image/kernel equality. Specify the
  extension data and action: an arbitrary extension with the same endpoints
  is not the FLM construction.
- Prove that the transformations of $B$ preserve its product and required
  form, and act faithfully. Prove order formulas from the verified extension.

The dot does not assert a splitting. Distinguish the central extension
$1\to Z(Q)\to Q\to Q/Z(Q)\to1$ from the larger extension:
$Q$ need not be central in $H$.

## Prerequisites and external inputs

Background includes finite 2-groups, centers, commutators, Frattini subgroups,
quotients, central extensions, and characteristic-two quadratic forms.
The lattice model, cocycle, and finite representations must follow the audited
source argument. The external Griess-algebra workstream supplies the concrete
product, form, and conventions; dimension alone does not specify the algebra.

Use the existing GroupExtension and central-commutator infrastructure where
applicable; see the [library audit](../../sources/library-audit.md).

## Completion criterion

The specific $Q$, $\mathrm{Co}_1$, $H$, maps, and faithful algebra
action must have checked constructions and proofs with all source prerequisites
discharged. A theorem assuming these properties is only an intermediate result.

## Source questions

- Locate each group definition, quotient map, and action formula in FLM.
- Fix the lattice model, cocycle, quadratic-form convention, and representation;
  find the plus-type proof and Conway-group facts actually invoked.
- Trace the references proving the required Conway-group properties.
- Locate the later involution-centralizer identification: constructing $H$
  does not yet prove that it is a centralizer in the generated group.

## Sources

- [FLM passage checklist](../../sources/flm.md)
- [Project-authored scope](../../sources/scope.md)
