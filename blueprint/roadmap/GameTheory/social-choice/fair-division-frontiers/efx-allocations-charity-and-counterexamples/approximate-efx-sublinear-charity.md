# (1 - epsilon)-EFX with sublinearly many unallocated goods

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every $\varepsilon \in (0, \tfrac12]$ there is a partial allocation $X$ with pool $P$ that is $(1 - \varepsilon)$-EFX, in which no agent envies the pool, and with

$$
\lvert P \rvert = O\!\left(\sqrt{n/\varepsilon}\right);
$$

moreover the Nash welfare of $X$ is at least half the maximum Nash welfare. More generally the number of unallocated goods can be bounded by a function of the rainbow cycle number, giving $O((n/\varepsilon)^{4/5})$ from $R(d) \le d^4$.

## Proof sketch

Group the agents' bundles by value scale into $O(1/\varepsilon)$-granular classes and build an auxiliary multipartite graph whose parts are pool goods and whose arcs record which agent would accept which good while maintaining $(1-\varepsilon)$-EFX. If the pool is large, the graph satisfies the in-arc condition of the rainbow cycle number definition, so a rainbow cycle exists; reallocating along it strictly improves a potential while preserving approximate EFX. Hence the pool size is bounded via $R(d)$, and the bound $R(d) = O(d \log d)$ gives the stated estimate.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Rainbow cycle number](rainbow-cycle-number.md)
- [Nash Welfare](../../../not-yet-classified/part-01/indivisible/nash-welfare.md)

## Proof depends on

- [Upper bounds on the rainbow cycle number](rainbow-cycle-number-upper-bounds.md)
- [EFX with bounded charity: fewer than n goods left unallocated](efx-with-bounded-charity.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, P. Misra, "Improving EFX Guarantees through Rainbow Cycle Number", EC 2021, arXiv:2103.01628.
- H. Akrami, N. Alon, B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, "EFX: A Simpler Approach and an (Almost) Optimal Guarantee via Rainbow Cycle Number", EC 2023; Operations Research (2024); arXiv:2205.07638 (titled "EFX Allocations: Simplifications and Improvements").
