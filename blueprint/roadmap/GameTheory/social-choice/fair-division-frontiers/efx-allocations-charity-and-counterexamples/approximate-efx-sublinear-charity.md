# (1 - epsilon)-EFX with sublinearly many unallocated goods

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every $\varepsilon \in (0, \tfrac12]$ there is a partial allocation $X$ with pool $P$ that is $(1 - \varepsilon)$-EFX and has

$$
\lvert P \rvert = \tilde O\!\left(\sqrt{n/\varepsilon}\right).
$$

More generally, with $h(d) = d \cdot R(d)$ for the rainbow cycle number $R$, a $(1 - \varepsilon)$-EFX partial allocation exists with $O\bigl(n / (\varepsilon\, h^{-1}(n/\varepsilon))\bigr)$ unallocated goods. The bound $R(d) \le d^4 + d$ gives $\lvert P \rvert \le 64 (n/\varepsilon)^{4/5}$, achievable in polynomial time, and a modification of that algorithm also outputs an allocation whose Nash social welfare $\mathrm{NSW}(X) = \bigl(\prod_{i=1}^n v_i(X_i)\bigr)^{1/n}$, the geometric mean of the agents' values, is at least $1/(2e^{1/e})$ times its maximum over complete allocations, that is, a $2e^{1/e} \approx 2.88$-approximation of the maximum Nash social welfare; the bound $R(d) = O(d \log d)$ gives the displayed estimate, again in polynomial time and with the same Nash social welfare guarantee.

## Proof sketch

Maintain a $(1-\varepsilon)$-EFX partial allocation with an acyclic envy graph and apply update rules that either allocate a pool good without decreasing any value or produce a Pareto-dominating $(1-\varepsilon)$-EFX allocation. When no rule applies, split the pool into high-demand goods, of which there are at most $2n/(\varepsilon d)$, and low-demand goods. The low-demand goods define an auxiliary multipartite digraph with parts of size at most $d$ in which every vertex has an in-arc from every other part; if it has more than $R(d)$ parts it contains a rainbow cycle, along which a Pareto improvement exists. Hence the pool has $O(\max(2n/(\varepsilon d), R(d)))$ goods, and choosing $d$ optimally gives the bounds.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Rainbow cycle number](rainbow-cycle-number.md)
- [Nash Welfare](../../../not-yet-classified/part-01/indivisible/nash-welfare.md)
- [Approximation ratio for the Nash social welfare objective](../nash-welfare-fairness-guarantees/nash-social-welfare-approximation-ratio.md)

## Proof depends on

- [Upper bounds on the rainbow cycle number](rainbow-cycle-number-upper-bounds.md)
- [EFX with bounded charity: fewer than n goods left unallocated](efx-with-bounded-charity.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, P. Misra, "Improving EFX Guarantees through Rainbow Cycle Number", EC 2021, arXiv:2103.01628.
- H. Akrami, N. Alon, B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, "EFX: A Simpler Approach and an (Almost) Optimal Guarantee via Rainbow Cycle Number", EC 2023; Operations Research (2024); arXiv:2205.07638 (titled "EFX Allocations: Simplifications and Improvements").
