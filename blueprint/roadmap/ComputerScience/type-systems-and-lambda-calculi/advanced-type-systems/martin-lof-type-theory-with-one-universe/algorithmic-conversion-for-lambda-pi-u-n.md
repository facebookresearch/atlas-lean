# Algorithmic conversion for λΠUN

For [λΠUN](the-type-theory-lambda-pi-u-n.md), six relations are defined simultaneously, each pair consisting of a relation on weak head normal forms and one that
first [weak-head reduces](typed-weak-head-reduction-in-lambda-pi-u-n.md):

- neutral equality $\Gamma \vdash n \leftrightarrow m : A$: equal variables; applications $n\, t \leftrightarrow m\, u$ when $n \leftrightarrow m : \Pi\, F\, G$ and $t \Leftrightarrow u : F$; $\mathsf{natrec}$ with
  componentwise equal motive, cases and neutral scrutinees; and the variant that reduces the type $A$ to weak head normal form;
- type equality $\Gamma \vdash A \Leftrightarrow B$: reduce both sides to weak head normal form, then $\mathsf{U} \Leftrightarrow \mathsf{U}$, $\mathsf{N} \Leftrightarrow \mathsf{N}$, $\Pi\, F\, G \Leftrightarrow \Pi\, H\, E$ componentwise, or neutral types equal as
  neutrals of type $\mathsf{U}$;
- term equality $\Gamma \vdash t \Leftrightarrow u : A$: reduce the type and both terms to weak head normal form, then compare types as terms of $\mathsf{U}$, $\mathsf{zero}$ and $\mathsf{suc}$
  structurally at $\mathsf{N}$, neutrals at $\mathsf{N}$ or at a neutral type as neutrals, and functions at $\Pi\, F\, G$ by η: $f \Leftrightarrow g$ if $f[\uparrow]\, i_0 \Leftrightarrow g[\uparrow]\, i_0 : G$.

The type-directed η-rule makes the checker complete for the extensionality rule of the declarative system.

## Depends on

- [Typed weak head reduction in λΠUN](typed-weak-head-reduction-in-lambda-pi-u-n.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.1 and Figure 6 (algorithm for conversion of neutrals, types and terms).
