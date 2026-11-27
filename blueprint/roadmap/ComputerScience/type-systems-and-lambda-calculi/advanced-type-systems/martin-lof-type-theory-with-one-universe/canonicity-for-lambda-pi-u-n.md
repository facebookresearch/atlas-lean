# Canonicity for λΠUN

In [λΠUN](the-type-theory-lambda-pi-u-n.md), every closed term of type $\mathsf{N}$ is convertible to a numeral: if $\epsilon \vdash t : \mathsf{N}$, then
$\epsilon \vdash t = \mathsf{suc}^n\, \mathsf{zero} : \mathsf{N}$ for some $n \in \mathbb{N}$. The proof is by the fundamental theorem of a Kripke logical relation of reducibility, which makes every
well-formed term reducible.

## Depends on

- [The type theory λΠUN](the-type-theory-lambda-pi-u-n.md)

## Expansion

This page becomes ready once:

- The Kripke logical relation of reducibility for λΠUN, its fundamental theorem and the corollary that every well-formed object is reducible (Theorem 3.21 and Corollary 3.22 of the source) (proof prerequisite; not yet stated)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 3 (the logical relation and Theorem 3.21, the fundamental theorem) and Theorem 3.24 (canonicity).
