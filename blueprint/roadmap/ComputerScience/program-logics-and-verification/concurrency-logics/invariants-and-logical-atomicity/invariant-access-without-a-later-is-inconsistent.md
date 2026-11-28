# Invariant access without a later is inconsistent

If the Iris rule for accessing an invariant were strengthened to give the invariant's content without a later, Iris would be inconsistent for a suitable choice of resource algebra.

**Theorem.** Suppose Iris is extended with the rule: for $\iota \in \mathcal{E}$,

$$
\boxed{P}^{\iota} \vdash {}^{\mathcal{E}}|\!\Rrightarrow^{\mathcal{E} \setminus \{\iota\}} \big(P \ast (P \mathrel{-\!\!\ast} {}^{\mathcal{E} \setminus \{\iota\}}|\!\Rrightarrow^{\mathcal{E}} \mathrm{True})\big).
$$

Then, for an appropriate choice of resource algebra, $\mathrm{True} \vdash |\!\Rrightarrow_{\top} \mathrm{False}$.

## Depends on

- [Fancy update modality](fancy-update-modality.md)
- [World satisfaction](world-satisfaction.md)

## Proof depends on

- [Impredicative invariants paradox](impredicative-invariants-paradox.md)
- [Fancy update modality](fancy-update-modality.md)
- [World satisfaction](world-satisfaction.md)

## Expansion

The rule is the invariant access rule with the later on $P$ removed. The source derives the theorem from the general paradox: Iris's fancy updates with masks $\emptyset$ and $\top$ satisfy the strong monad and mask-weakening hypotheses, Iris's invariants satisfy allocation and persistence, the added rule gives opening without a later, and a resource algebra with a two-state one-way token protocol provides $S$ and $F$.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 8.2, Theorem 8 and its relation to Theorem 9.
