# Integrated heterozygote count of a new neutral mutant

For the neutral Wright–Fisher diffusion started at frequency $x$, with time in units of $2N$ generations and absorption time $\tau$, the expected integral of the heterozygosity until absorption is $E\bigl[\int_0^\tau2X_s(1 - X_s)\,ds\bigr] = 2x(1 - x)$. Maruyama and Kimura (1975, abstract) use their moment formulas for sums of a function of gene frequency along sample paths to compute the total frequency of heterozygotes involving an allele since its origin. Converting to counts (derivation): in a population of $N$ diploids in Hardy–Weinberg proportions, the expected number of heterozygous carriers in a generation at frequency $x$ is $N\cdot2x(1 - x)$, and one unit of diffusion time is $2N$ generations, so the expected total number of heterozygote-generations over the lifetime of an allele started at $x$ is

$$2N\cdot N\cdot2x(1 - x) = 4N^2x(1 - x).$$

For a new mutation, $x = 1/(2N)$, this equals $2N - 1$: in the diffusion approximation a new neutral mutant is carried, summed over its whole history, by $2N - 1$ heterozygous individual-generations on average.

## Depends on

- [Expected integral of heterozygosity until absorption](../../absorption-of-the-neutral-wright-fisher-martinga/integral-two-mul-one-sub-absorption-time.md)
- [Moment recursion for additive path functionals](../../../../../Probability/stochastic-calculus/one-dimensional-diffusions/kac-maruyama-kimura-moment-recursion.md)

## Expansion

1. The functionals $\int_0^\tau X_s\,ds$, $\int_0^\tau X_s^2\,ds$ and $\int_0^\tau2X_s(1 - X_s)\,ds$ and their meaning as integrated allele, homozygote and heterozygote frequencies.
2. Their expectations from the Green's function, for neutral and selected alleles, started at $1/(2N)$.
3. Their variances from the moment recursion.
4. Conversion of diffusion-time integrals into counts of gene copies and of individuals, with the factors $2N$ and $N$.

## Sources

- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
