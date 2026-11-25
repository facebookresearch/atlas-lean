# Measurable partition modulo null sets

Let $(X, \mu)$ be a measure space and $I$ an index set. A family $\xi = (C_i)_{i \in I}$ of subsets of $X$ is a
measurable partition of $(X, \mu)$ modulo null sets if

- every atom $C_i$ is measurable;
- distinct atoms are almost disjoint: $\mu(C_i \cap C_j) = 0$ for $i \ne j$;
- the atoms cover almost all of $X$: $\mu\bigl(X \setminus \bigcup_{i \in I} C_i\bigr) = 0$.

The definition does not require $I$ to be finite; the [entropy of a partition](partition-entropy.md) and the
[Kolmogorov–Sinai entropy](ks-entropy.md) use partitions with finitely many atoms.
