# Benjamini–Hochberg FDR control

Let $\mu$ be a probability measure on $\Omega$, $m \in \mathbb{N}$ and $p_0, \dots, p_{m-1} : \Omega \to \mathbb{R}$ measurable and mutually independent, and let $H_0 \subseteq \{0, \dots, m-1\}$ be the set of true nulls, each $p_i$ with $i \in H_0$ being uniformly distributed on $[0, 1]$. For every $q \in [0, 1]$, the Benjamini–Hochberg procedure at level $q$ has false discovery rate at most $q|H_0|/m$:

$$\mathbb{E}_\mu\big[\mathrm{FDP}(H_0, R)\big] \le \frac{q\,|H_0|}{m},$$

where $R$ is the [Benjamini–Hochberg rejection set](bh-rejections.md) of $(p_0(\omega), \dots, p_{m-1}(\omega))$ and $\mathrm{FDP}$ the [false discovery proportion](../valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md). Nothing is assumed about the false-null p-values beyond measurability and independence. For $m = 0$ both sides are $0$. The same bound holds for valid (super-uniform) true-null p-values.

## Sources

- Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful approach to multiple testing*, J. Roy. Statist. Soc. Ser. B 57 (1995), 289–300, Theorem 1.
