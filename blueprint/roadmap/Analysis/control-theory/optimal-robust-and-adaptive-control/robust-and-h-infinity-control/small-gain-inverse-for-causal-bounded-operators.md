# Small-gain inverse for causal bounded operators

Let $\mathbb{T}$ be $\mathbb{Z}$, $\mathbb{N}$, $\mathbb{R}$ or $[0, \infty)$, let $X$ be a Banach space of signals on $\mathbb{T}$, and for each $t \in \mathbb{T}$ let $P_t : X \to X$ be a bounded linear projection, the truncation to times at most $t$, with $P_s P_t = P_{\min(s,t)}$. A bounded linear operator $G : X \to X$ is **causal** if $P_t G = P_t G P_t$ for every $t$: the output up to time $t$ depends only on the input up to time $t$. Write $\|G\|$ for the operator norm. For instance, $X = \ell^2(\mathbb{N}; \mathbb{R}^k)$ with $(P_t x)(n) = x(n)$ for $n \le t$ and $0$ otherwise.

1. **The causal operators form a closed algebra.** They contain the identity and are closed under sums, scalar multiples, composition and limits in operator norm.
2. **Small-gain inverse.** If $G$ and $K$ are causal and $\|G\|\,\|K\| < 1$, then $I + GK$ is invertible, its inverse is causal and given by the norm-convergent series $\sum_{n \ge 0} (-GK)^n$, and

    $$\big\|(I + GK)^{-1}\big\| \le \frac{1}{1 - \|G\|\,\|K\|}.$$

3. **Robustness to an additive perturbation.** If $G$, $K$ and $\Delta$ are causal and $(\|G\| + \|\Delta\|)\,\|K\| < 1$, then $I + (G + \Delta)K$ is invertible with causal inverse of norm at most $1/\big(1 - (\|G\| + \|\Delta\|)\|K\|\big)$.

In the feedback loop $e = r - Ky$, $y = Ge$, part 2 with the roles of $G$ and $K$ exchanged says that $r \mapsto e = (I + KG)^{-1} r$, and hence $r \mapsto y = Ge$, is a causal bounded operator; the case $G = 0$ needs no separate treatment.

**Proof.** For part 1, if $G$ and $H$ are causal then $P_t G H = P_t G P_t H = P_t G P_t H P_t = P_t G H P_t$, sums and scalar multiples are immediate, and if $G_n \to G$ in norm with each $G_n$ causal then $P_t G - P_t G P_t = \lim_n (P_t G_n - P_t G_n P_t) = 0$. For part 2, $\|(-GK)^n\| \le (\|G\|\|K\|)^n$, so the series converges absolutely in the Banach algebra of bounded operators; its partial sums $S_N$ are causal and satisfy $(I + GK) S_N = S_N (I + GK) = I - (-GK)^{N+1}$, so the limit $S$ is a two-sided inverse, causal by part 1, with $\|S\| \le \sum_n (\|G\|\|K\|)^n$. Part 3 is part 2 applied to $G + \Delta$, using $\|G + \Delta\| \le \|G\| + \|\Delta\|$.

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 10.5, Theorem 10.4 (small gain theorem, p. 10-24): a feedback interconnection of input/output stable systems with gains $\gamma_1, \gamma_2$ and $\gamma_1 \gamma_2 < 1$ is input/output stable with gain $\gamma_1/(1 - \gamma_1\gamma_2)$, stated with "properly defined" signal spaces. The causal operator algebra, the Neumann-series inverse and the perturbation bound are derived on the page for bounded linear operators.
