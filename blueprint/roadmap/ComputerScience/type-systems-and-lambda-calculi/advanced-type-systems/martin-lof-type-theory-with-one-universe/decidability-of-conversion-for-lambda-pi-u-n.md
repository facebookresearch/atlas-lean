# Decidability of conversion for λΠUN

In [λΠUN](the-type-theory-lambda-pi-u-n.md), conversion is decidable on well-formed inputs: if $\Gamma \vdash A$ and $\Gamma \vdash B$ it is decidable whether $\Gamma \vdash A = B$, and if
$\Gamma \vdash t : A$ and $\Gamma \vdash u : A$ it is decidable whether $\Gamma \vdash t = u : A$. The algorithmic checker decides it, being sound, complete, and decidable on such inputs.

## Depends on

- [The type theory λΠUN](the-type-theory-lambda-pi-u-n.md)

## Proof depends on

- [Soundness of algorithmic conversion for dependent type theory](../soundness-of-algorithmic-conversion-for.md)
- [Completeness of algorithmic conversion for λΠUN](completeness-of-algorithmic-conversion-for-lambda.md)
- [Decidability of algorithmic conversion for λΠUN](decidability-of-algorithmic-conversion-for-lambda.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.2, Theorem 4.12 (decidability of conversion).
