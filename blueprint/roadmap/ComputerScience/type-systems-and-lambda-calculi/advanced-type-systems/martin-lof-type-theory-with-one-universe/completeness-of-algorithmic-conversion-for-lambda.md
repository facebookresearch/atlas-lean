# Completeness of algorithmic conversion for λΠUN

In λΠUN, declarative conversion implies [algorithmic conversion](algorithmic-conversion-for-lambda-pi-u-n.md): if $\Gamma \vdash A = B$ then $\Gamma \vdash A \Leftrightarrow B$, and if
$\Gamma \vdash t = u : A$ then $\Gamma \vdash t \Leftrightarrow u : A$. The proof instantiates the generic equality of the logical relation with algorithmic conversion, which requires its
symmetry, transitivity, weakening and the lifting of weak head normal forms and of neutrals, and applies the fundamental theorem.

## Depends on

- [Algorithmic conversion for λΠUN](algorithmic-conversion-for-lambda-pi-u-n.md)

## Proof depends on

- [Soundness of algorithmic conversion for dependent type theory](../soundness-of-algorithmic-conversion-for.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.2, Lemmas 4.6–4.10, Instance 2 (algorithmic equality instance) and Theorem 4.11 (completeness of algorithmic equality).
