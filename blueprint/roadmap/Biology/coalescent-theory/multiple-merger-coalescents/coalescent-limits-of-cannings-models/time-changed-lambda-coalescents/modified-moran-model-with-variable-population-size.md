# Modified Moran model with variable population size

**Fixed size.** Let $N \ge 2$ and let $U_N(z)$, $z \in \mathbb Z$, be i.i.d. random variables with values in $\{2, \dots, N\}$ and common law $U_N$. In each generation $z$ of the haploid **modified Moran model**:

- one uniformly chosen individual has $U_N(z)$ offspring;
- $U_N(z) - 1$ uniformly chosen other individuals have no offspring;
- the remaining $N - U_N(z)$ individuals have one offspring each.

For a finite measure $\Lambda$ on $[0, 1]$ with $\Lambda([0, 1]) = 1$, let $U'_N$ be distributed as the size of the first merger of a $\Lambda$-coalescent started from $N$ blocks (Eq. 6):

$$\mathbb P(U'_N = j) = \lambda_N^{-1} \binom{N}{j}\, \mathbb E\big[X^{j-2} (1 - X)^{N-j}\big], \qquad 2 \le j \le N,$$

where $X \sim \Lambda$ and $\lambda_N$ is the total merger rate of the $\Lambda$-coalescent with $N$ blocks. The fixed-size model with $U_N = U'_N$ has rescaled genealogies converging to the $\Lambda$-coalescent.

**Variable size.** Let $N_r$ be the population size $r$ generations in the past, $N = N_0$. To pass from generation $r$ to generation $r - 1$, first run one step of the fixed-$N_r$ model. If $N_{r-1} < N_r$, sample $N_{r-1}$ of the $N_r$ potential offspring without replacement. If $d_{N, r} = N_{r-1} - N_r > 0$ (Eq. 7), add $A_{N, r}$ further offspring to the multiplying parent and $d_{N, r} - A_{N, r}$ offspring to parents that had no offspring (at most $U_{N_r} - 1$ of them). The multiplying parent then has $U_{N, r} = U_{N_r} + A_{N, r}$ offspring and every other offspring has a distinct parent.

**Size profile** (Eq. 4). With $c_N$ the pair-coalescence probability of the fixed-$N$ model, one assumes that for each $t > 0$ and all $0 \le r \le \lfloor c_N^{-1} t \rfloor$,

$$c_1(t) N \le N_r \le c_2(t) N, \qquad N^{-1} N_{\lfloor t c_N^{-1} \rfloor} \to \nu(t) \quad (N \to \infty),$$

for positive finite functions $c_1, c_2, \nu$ on $[0, \infty)$; $\nu$ is the population size profile in coalescent time.

## Depends on

- [Cannings model of a haploid population](../../cannings-models/cannings-model.md)
- [The Λ-coalescent rate matrix on partitions of a finite sample](../../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [Total merger rate of a Λ-coalescent](../../../coalescents/total-merger-rate.md)
- [Coalescence probability of a Cannings model](../../cannings-models/coal-prob.md)

## Expansion

Only one parent can have more than one offspring per generation, so the ancestral partition of a sample can undergo at most one merger per generation; the law of $U_N$ tunes which merger sizes occur. The size-changing step either thins the offspring (decline) or pads it (growth) while keeping the one-multiplying-parent structure, so the one-generation merger probabilities remain explicit functions of $N_r$ and $U_{N_r}$.

## Sources

- F. Freund, *Cannings models, population size changes and multiple-merger coalescents*, J. Math. Biol. (2020). <https://doi.org/10.1007/s00285-020-01470-5> (PMCID: PMC7052052)
