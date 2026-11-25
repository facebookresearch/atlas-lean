# Harmony lemma for the pi-calculus

The $\pi$-calculus has two operational semantics.
- The **reduction semantics** is a relation $P \to Q$ defined modulo structural congruence $\equiv$. Structural congruence makes parallel composition associative and commutative with unit $\mathbf{0}$, and allows the extension of the scope of a restriction: $(\nu x)P \mid Q \equiv (\nu x)(P \mid Q)$ when $x$ is not free in $Q$. Reduction is closed under $\equiv$, so if $P \equiv P'$, $P' \to Q'$ and $Q' \equiv Q$, then $P \to Q$.
- The **labelled transition semantics** has transitions $P \xrightarrow{\alpha} Q$ with actions $\alpha$: input $x(y)$, free output $\bar x y$, bound output $\bar x(y)$ and the internal action $\tau$. Its open and close rules handle scope extrusion directly.

The harmony lemma relates them:

1. If $P \equiv P'$ and $P' \xrightarrow{\alpha} Q$, then $P \xrightarrow{\alpha} Q'$ for some $Q' \equiv Q$. Structural congruence is a strong bisimulation for the labelled semantics.
2. $P \to Q$ if and only if $P \xrightarrow{\tau} Q'$ for some $Q' \equiv Q$.

A complete machine-checked proof, in the logical framework Beluga, covers the fragment with $\mathbf{0}$, input and output prefixes, parallel composition and restriction, without sums or replication. That development also proves the equivalence of the early and late transition semantics.

## Background

- [Reachability in a labelled transition system is transitive](../labelled-transition-systems/trans.md)

## Sources

- G. Cecilia and A. Momigliano, "A Beluga formalization of the harmony lemma in the π-calculus", *Logical Frameworks and Meta-Languages: Theory and Practice (LFMTP 2024)*, EPTCS 404, 2024, pp. 1–17, <https://gabrielececilia.github.io/papers/lfmpt24-paper.pdf>: Section 2 (syntax of the fragment, Figure 1 with structural congruence and reduction, the labelled transition system) and Section 2.4 (the harmony lemma as stated by Sangiorgi and Walker, parts i and ii).
