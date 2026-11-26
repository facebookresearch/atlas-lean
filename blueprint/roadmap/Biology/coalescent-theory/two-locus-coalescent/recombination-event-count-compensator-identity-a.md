# Expected number of recombination events: compensator identity and two-locus value

In the reduced [coalescent with recombination](coalescent-with-recombination-ancestral-material.md) on $L$ loci with breakpoint rates $\rho_i \ge 0$, run up to its end $\tau_{\mathrm{red}}$, let $R$ count the recombination events on lineages whose material not yet at its most recent common ancestor lies on both sides of the breakpoint. Call this counting convention C; other conventions give other counts.

1. **Compensator identity.** With $k_i(t)$ the number of lineages whose material spans breakpoint $i$ under convention C,

$$\mathbb{E}[R] = \mathbb{E} \int_0^{\tau_{\mathrm{red}}} \frac{1}{2} \sum_i \rho_i\, k_i(t)\, dt,$$

by the [expected transition counts of a finite Markov chain up to a hitting time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/expected-transition-counts-of-a-finite-ctmc-up-t.md).

2. **Two loci.** For two loci with recombination rate $\rho$, two samples, started from the linked state,

$$\mathbb{E}[R] = \frac{2\rho\,(2\rho + 9)}{\rho^2 + 13\rho + 18},$$

computed with [the two-locus rate matrix](two-locus-rate.md).

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](coalescent-with-recombination-ancestral-material.md)
- [Expected transition counts of a finite Markov chain up to a hitting time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/expected-transition-counts-of-a-finite-ctmc-up-t.md)
- [Rate matrix of the two-locus coalescent](two-locus-rate.md)

## Proof depends on

- [Covariance of the coalescence times, path form](covariance-coalescence-times.md)

## Expansion

1. The compensator identity under convention C.
2. The two-locus value by first-step analysis. Exact checks: $\rho = 1$ gives $11/16$, $\rho = 3$ gives $15/11$ and $\rho = 1/2$ gives $40/99$. As $\rho \to 0$, $\mathbb{E}[R] \sim \rho$, and as $\rho \to \infty$, $\mathbb{E}[R] \to 4$.
3. A three-locus check of the convention: with $\rho_1 = \rho_2 = 1$, a lineage whose material spans only loci $1$ and $2$ contributes split rate $1/2$, not $\rho/2 = 1$.
4. The relation between convention C and the counting convention of Hudson and Kaplan (1985), and the comparison of part 2 with their closed form.

## Sources

- R. R. Hudson and N. L. Kaplan, Statistical properties of the number of recombination events in the history of a sample of DNA sequences, *Genetics* 111 (1985), 147–164, <https://pubmed.ncbi.nlm.nih.gov/4029609/> (mean and variance of the number of recombination events).
- R. C. Griffiths, The two-locus ancestral graph, in *Selected Proceedings of the Sheffield Symposium on Applied Probability*, IMS Lecture Notes 18 (1991), 100–117 (two-locus ancestral graph).
