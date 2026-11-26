# Decidability of algorithmic conversion for λΠUN

Let $\vdash \Gamma = \Delta$ (contexts pointwise convertible). For [the algorithmic conversion relations](algorithmic-conversion-for-lambda-pi-u-n.md) of λΠUN:

1. if $\Gamma \vdash t \leftrightarrow t : A$ and $\Delta \vdash u \leftrightarrow u : B$, it is decidable whether $\Gamma \vdash t \leftrightarrow u : C$ for some $C$;
2. if $\Gamma \vdash A \Leftrightarrow A$ and $\Delta \vdash B \Leftrightarrow B$, it is decidable whether $\Gamma \vdash A \Leftrightarrow B$;
3. if $\Gamma \vdash t \Leftrightarrow t : A$ and $\Delta \vdash u \Leftrightarrow u : A$, it is decidable whether $\Gamma \vdash t \Leftrightarrow u : A$.

The hypotheses that each side is related to itself supply the termination measure.

## Depends on

- [Algorithmic conversion for λΠUN](algorithmic-conversion-for-lambda-pi-u-n.md)

## Proof depends on

- [Π-injectivity and syntactic validity for λΠUN](pi-injectivity-and-syntactic-validity-for-lambda-pi-u-n.md)
- [Weak head normalization for λΠUN](weak-head-normalization-for-lambda-pi-u-n.md)
- [Soundness of algorithmic conversion for dependent type theory](../soundness-of-algorithmic-conversion-for.md)

## Sources

- A. Abel, J. Öhman and A. Vezzosi, "Decidability of conversion for type theory in type theory", *Proceedings of the ACM on Programming Languages* 2(POPL), Article 23, 2018, <https://doi.org/10.1145/3158111>: Section 4.2, the definition of context equality, Lemmas 4.1–4.4 and Theorem 4.5 (decidability of algorithmic equality).
