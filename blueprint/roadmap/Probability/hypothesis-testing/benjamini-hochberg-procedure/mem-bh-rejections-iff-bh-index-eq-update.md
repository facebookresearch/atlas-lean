# Benjamini–Hochberg rejection as leave-one-out index invariance

Let $m \in \mathbb{N}$, $q \ge 0$, $p_0, \dots, p_{m-1} \in \mathbb{R}$ and $i \in \{0, \dots, m-1\}$. Let $p^{(i \to 0)}$ be the vector $p$ with its $i$-th entry replaced by $0$. Then the Benjamini–Hochberg procedure at level $q$ rejects hypothesis $i$ if and only if

$$k^*(p) = k^*(p^{(i \to 0)}),$$

where $k^*$ is the [step-up index](bh-index.md). No sign condition is imposed on the p-values.

## Sources

- W. Fithian and L. Lei, *Conditional calibration for false discovery rate control under dependence*, arXiv:2007.10438 (2020), Lemma 1, stated there for general step-up procedures.
