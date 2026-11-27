# Weak head normalization for λΠUN

In [λΠUN](the-type-theory-lambda-pi-u-n.md), every well-formed type and every well-typed term [weak-head reduces](typed-weak-head-reduction-in-lambda-pi-u-n.md) to a weak head normal
form: if $\Gamma \vdash A$ then $\Gamma \vdash A \longrightarrow^* \bar A$ for some weak head normal form $\bar A$, and if $\Gamma \vdash t : A$ then $\Gamma \vdash t \longrightarrow^* \bar t : A$ for some weak head normal
form $\bar t$.

## Depends on

- [Typed weak head reduction in λΠUN](typed-weak-head-reduction-in-lambda-pi-u-n.md)

## Expansion

This page becomes ready once:

- The Kripke logical relation of reducibility for λΠUN, its fundamental theorem and the corollary that every well-formed object is reducible (Theorem 3.21 and Corollary 3.22 of the source) (proof prerequisite; not yet stated)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 3.6, Theorem 3.28 (weak head normalization).
