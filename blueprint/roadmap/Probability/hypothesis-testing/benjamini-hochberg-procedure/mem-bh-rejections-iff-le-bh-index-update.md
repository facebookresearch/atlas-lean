# Leave-one-out criterion for Benjamini–Hochberg rejection

Let $m \in \mathbb{N}$, $q \ge 0$, $p_0, \dots, p_{m-1} \in \mathbb{R}$ and $i \in \{0, \dots, m-1\}$. Let $k^0 = k^*(p^{(i \to 0)})$ be the [step-up index](bh-index.md) computed after replacing the $i$-th p-value by $0$. Then the Benjamini–Hochberg procedure at level $q$ rejects hypothesis $i$ if and only if

$$p_i \le \frac{q k^0}{m}.$$

No sign condition is imposed on the p-values.

## Sources

- W. Fithian and L. Lei, *Conditional calibration for false discovery rate control under dependence*, arXiv:2007.10438 (2020), Lemma 1, stated there for general step-up procedures.
