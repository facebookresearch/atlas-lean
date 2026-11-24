# Maynard's Proposition 4.2, reduction to the asymptotics of Proposition 4.1

Let $H$ be a finite set of shifts, $k \in \mathbb N$, $\theta > 0$, $\delta_0 > 0$ and $\rho \in \mathbb R$. If

$$\rho < \frac{\theta\, M_k}{2},$$

and for every [admissible profile](is-maynard-profile.md) $F$ and every $\delta \in (0, \delta_0)$ there are weights $w_N \ge 0$ and $B(N) > 0$ (for large $N$) with $S_1/B \to I_k(F)$ and $S_2/B \to (\theta/2 - \delta) \sum_m J_k^{(m)}(F)$, then infinitely many $n$ have more than $\rho$ of the $n + h$ prime. Taking $\rho = m$ gives $m + 1$ primes. Under Elliott–Halberstam, with $\theta = 1 - \varepsilon$, the condition is essentially $M_k > 2m$; with the Bombieri–Vinogradov level $\theta = \tfrac12 - \varepsilon$ it is essentially $M_k > 4m$. In the intended application $H$ is admissible with $\#H = k$; the statement does not tie $k$ to $H$, and the hypothesis can only hold if $\delta_0 \le \theta/2$ (for $k \ge 1$ a limit of non-negative sums cannot be negative).

Relation to the source. This is the first conclusion of Maynard (2015), Proposition 4.2, with $r_k = \lceil \theta M_k / 2 \rceil$ replaced by "more than $\rho$" for every $\rho < \theta M_k / 2$; the two are equivalent. The asymptotics are taken as hypotheses, and the weights in them are unconstrained: for each profile $F$ and each $\delta$, some non-negative weights must achieve the two limits. This abstracts Maynard's Proposition 4.1, which gives such limits for smooth $F$ with his sieve weights. The hypotheses are satisfiable for every admissible profile, smooth or not: if $H$ is admissible with $\#H = k$, $\theta$ is a level of distribution and $\delta_0 \le \theta/2$, then $c = (\theta/2 - \delta)\, \sum_m J_k^{(m)}(F) / I_k(F)$ lies in $(0, \theta M_k/2)$; Maynard's argument for a smooth near-optimal profile gives, for large $N$, some $n_1 \in [N, 2N)$ with more than $c$ primes among the $n_1 + h$, the Chinese remainder theorem gives $n_0 \in [N, 2N)$ with none, and the weights $\alpha \mathbf 1_{n_1} + \beta \mathbf 1_{n_0}$ in the right proportion achieve both limits exactly. A non-degenerate example of the hypotheses of the limiting step is given with [the limiting step](infinite-lt-prime-shift-count-of-tendsto.md). The second conclusion of Proposition 4.2, $\liminf_n (p_{n + r_k - 1} - p_n) \le \max_{i, j} (h_i - h_j)$, is [the bridge to prime gaps](frequently-nth-prime-add-sub-le-of-infin.md).

The proof picks, by the definition of the supremum, a profile $F$ with $\rho < \tfrac{\theta}{2} \sum_m J_k^{(m)}(F) / I_k(F)$ and applies [the reduction for one profile](infinite-lt-prime-shift-count-of-maynard.md). It needs no upper bound on the ratios: a real supremum of a nonempty set that exceeds $2\rho/\theta$ is exceeded by an element of the set, and [admissible profiles exist](exists-is-maynard-profile.md).

## Informally uses

- [Maynard's reduction for one weight profile](infinite-lt-prime-shift-count-of-maynard.md): the limiting argument for the chosen profile.
- [Maynard's variational quantity $M_k$](maynard-m.md): the supremum that is approached.

## Related topics

- [$M_5 > 2$](two-lt-maynard-m-five.md), [$M_{105} > 4$](four-lt-maynard-m-105.md) and [growth of $M_k$](eventually-log-sub-lt-maynard-m.md): Maynard's Proposition 4.3, which feeds this reduction in the proofs of Theorems 1.1–1.4.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
