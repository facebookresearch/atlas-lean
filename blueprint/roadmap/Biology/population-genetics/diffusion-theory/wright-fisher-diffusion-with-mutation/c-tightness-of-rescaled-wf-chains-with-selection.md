# C-tightness of rescaled Wright–Fisher chains with selection and mutation

For $M$ gene copies, selection coefficient $s = \alpha / M$ and mutation probabilities $u_i = \theta_i / (2M)$, let $X^M$ be the Wright–Fisher frequency chain with selection and mutation: from frequency $x$, mutation gives the [frequency after mutation](mutated-freq.md) $p'$, genic selection gives $p'' = (1 + s) p' / (1 + s p')$, and the next frequency is $k/M$ with $k \sim \mathrm{Bin}(M, p'')$; for $s = 0$ this is the chain whose [drift](integral-binomial-mutated-freq-drift.md) is the mutation drift. Fix $T > 0$ and a compact set of parameters $(\alpha, \theta)$, and consider only $M$ larger than $\lvert\alpha\rvert$ and $\theta_i/2$ for every parameter in that set, so that $0 \le u_i \le 1$, $s > -1$ and the chain is well defined. Then, uniformly over that set:

1. the increments satisfy the fourth-moment bound

$$\mathbb{E}\bigl\lvert X^M_{\lfloor tM \rfloor} - X^M_{\lfloor rM \rfloor}\bigr\rvert^4 \le C\Bigl(\lvert t - r \rvert^2 + \frac{\lvert t - r \rvert}{M}\Bigr), \qquad 0 \le r \le t \le T,\ rM, tM \in \mathbb{Z};$$

2. the largest one-generation jump tends to $0$ in probability:

$$\mathbb{P}\Bigl(\max_{k \le MT} \lvert \Delta X^M_k \rvert > \varepsilon\Bigr) \le \frac{C T}{M \varepsilon^4}.$$

Hence the step processes $t \mapsto X^M_{\lfloor tM \rfloor}$ are C-tight in $D([0, T], [0, 1])$, and their linear interpolations are tight in $C([0, T])$.

## Depends on

- [Allele frequency after one generation of two-way mutation](mutated-freq.md)
- [Drift of the Wright–Fisher chain with mutation](integral-binomial-mutated-freq-drift.md)

## Proof depends on

- [Tightness of interpolated rescaled WF chains in C([0,T])](../wright-fisher-semigroup-and-moment-duality/tightness-of-interpolated-rescaled-wf-chains-in.md)
- [Neutral Wright–Fisher transition matrix](../../wright-fisher-markov-chain/wright-fisher.md)
- [Prokhorov's theorem: tight sets of probability measures are relatively compact](../../../../Probability/convergence-of-measures/prokhorov-theorem-on-a-polish-space.md)

## Expansion

1. The fourth-moment bound, from the binomial sampling and the drift of the chain.
2. The jump bound, by a union bound over the $\lfloor MT \rfloor$ generations with a one-generation fourth-moment bound $C/M^2$.
3. C-tightness from the two bounds, and the reduction for $\alpha = \theta = 0$ to [the tightness of the neutral interpolated chains](../wright-fisher-semigroup-and-moment-duality/tightness-of-interpolated-rescaled-wf-chains-in.md).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10, Section 1 (tightness criteria).
