# Tightness of interpolated rescaled Wright–Fisher chains in C([0,T])

Let $X^{(M)}$ be the neutral Wright–Fisher frequency chain on $M$ gene copies, fix $T > 0$, and let $Y^M$ be the piecewise-linear interpolation of $t \mapsto X^{(M)}_{\lfloor tM \rfloor}$. There is a constant $C$, independent of $M$ and of the starting point, such that

$$\mathbb{E}\bigl\lvert Y^M(t) - Y^M(s) \bigr\rvert^4 \le C\Bigl(\lvert t - s \rvert^2 + \frac{\lvert t - s \rvert}{M}\Bigr)$$

for grid times $s, t \in M^{-1}\mathbb{Z} \cap [0, T]$, and $\mathbb{E}\lvert Y^M(t) - Y^M(s)\rvert^4 \le C \lvert t - s \rvert^2$ for all $s, t \in [0, T]$. Hence the laws of $Y^M$ are tight in $C([0, T])$ by the Kolmogorov–Chentsov modulus criterion.

## Proof depends on

- [One generation of the neutral Wright–Fisher chain](wf-step.md)
- [Neutral Wright–Fisher transition matrix](../../wright-fisher-markov-chain/wright-fisher.md)
- [Kolmogorov–Chentsov tightness criterion in $C([0,T])$](../../../../Probability/convergence-of-measures/kolmogorov-chentsov-tightness-criterion.md)

## Expansion

1. The grid bound, from the fourth central moments of the binomial sampling in [one generation](wf-step.md). The $1/M$ term comes from the fourth central binomial moment $\mathbb{E}\bigl[(k/M - p)^4\bigr] = p(1 - p)\bigl(1 + 3(M - 2)p(1 - p)\bigr)/M^3 \le C/M^2$, summed over the generations.
2. The bound for all $s, t$: for $\lvert t - s \rvert \ge 1/M$, $\lvert t - s \rvert / M \le \lvert t - s \rvert^2$; within one generation the interpolation is linear and the one-step fourth moment is of order $M^{-2}$.
3. Tightness from the modulus criterion.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 3 (tightness) and Chapter 10, Section 1.
