# Wright–Fisher pair coalescence time against its exponential limit

In the neutral haploid [Wright–Fisher model](../../population-genetics/wright-fisher-markov-chain/wright-fisher.md) with $M \ge 2$ gene copies, two distinct copies have distinct parents in each generation with probability
$1 - 1/M$, independently, so their coalescence time $T$ in generations satisfies $\mathbb P(T > k) = (1 - 1/M)^k$ for $k \in \mathbb N$. Then:

- $T/M$ takes values in the lattice $\frac1M \mathbb N$, a Lebesgue-null set of full $T/M$-probability, so its total-variation distance from $\mathrm{Exp}(1)$ is exactly $1$ for every $M$: no rate in total variation exists.
- In Kolmogorov distance, $\sup_{x \ge 0} |\mathbb P(T/M > x) - e^{-x}| \le 1/M$. With $a = 1 - 1/M$ and $k = \lfloor Mx \rfloor$, write $a^k - e^{-x} = (a^k - e^{-k/M}) + (e^{-k/M} - e^{-x})$: the first term lies in $[-\frac{1}{eM}, 0]$, since $a \le e^{-1/M}$ and $a\,e^{1/M} \ge 1 - 1/M^2$ (from $(1 - u)e^u \ge (1 - u)(1 + u) = 1 - u^2$ on $[0, 1]$), giving $0 \le e^{-k/M} - a^k \le e^{-k/M} k/M^2 \le \frac{1}{eM}$; the second lies in $[0, 1 - e^{-1/M}] \subseteq [0, \frac1M]$. Having opposite signs, their sum is at most $\frac1M$ in absolute value.

The supremum equals $1 - e^{-1/M}$ and is approached, not attained, as $x \uparrow 1/M$: on $[k/M, (k+1)/M)$ the gap
$a^k - e^{-x}$ is at most $e^{-k/M}(1 - e^{-1/M}) \le 1 - e^{-1/M}$, with equality in the limit for $k = 0$, while $e^{-k/M} - a^k \le \frac{1}{eM} < 1 - e^{-1/M}$
for $M \ge 2$. This quantifies the [convergence of Wright–Fisher coalescence times to exponential laws](tendsto-no-coal-prob-pow-floor.md) for a pair.

## Depends on

- [Neutral Wright–Fisher transition matrix](../../population-genetics/wright-fisher-markov-chain/wright-fisher.md)

## Related topics

- [Wright–Fisher coalescence times converge to exponential laws](tendsto-no-coal-prob-pow-floor.md)

## Sources

- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008) (pair coalescence in the Wright–Fisher model). The bounds are derived above and checked numerically for M = 2, …, 200.
