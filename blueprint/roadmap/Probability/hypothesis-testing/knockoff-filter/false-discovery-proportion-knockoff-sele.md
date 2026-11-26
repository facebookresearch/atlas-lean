# The false discovery proportion of knockoff+ is bounded by a null-count ratio

Let $q \in \mathbb{R}$, $W \in \mathbb{R}^p$ and $H_0 \subseteq \{1, \dots, p\}$. If the knockoff+ threshold is a real number $T$, then the false discovery proportion of the knockoff+ selection $\hat S_1$ satisfies

$$\mathrm{FDP}(H_0, \hat S_1) \le \frac{q\,\#\{j \in H_0 : W_j \ge T\}}{1 + \#\{j \in H_0 : W_j \le -T\}}.$$

This is the deterministic first step of the proof of FDR control, after which it remains to bound the expectation of the ratio by $1$.

## Informally uses

- [The estimated false discovery proportion is at most $q$ at the threshold](knockoff-threshold-ratio-le.md): the defining property of $T$, combined with $\#\{j \in H_0 : W_j \le -T\} \le \#\{j : W_j \le -T\}$.

## Sources

- R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*, Ann. Statist. 43 (2015), arXiv:1404.5609, Section 2.4, equation (2.5).
