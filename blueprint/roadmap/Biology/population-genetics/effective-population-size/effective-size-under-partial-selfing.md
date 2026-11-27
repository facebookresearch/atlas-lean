# Effective size of a finite population with partial selfing

Consider $N \ge 2$ monoecious diploids per generation, with each offspring formed independently: with probability
$S \in [0, 1)$ both its genes are independent Mendelian draws from one uniformly chosen parent, and otherwise its two
genes come from two parents chosen independently and uniformly (possibly the same). Let $F_t$ be the probability
that the two genes of an individual are identical by descent and $\Theta_t$ the probability for two genes in distinct
individuals. Conditioning on the parents gives

$$\Theta_{t+1} = \frac1N \cdot \frac{1 + F_t}{2} + \Bigl(1 - \frac1N\Bigr) \Theta_t, \qquad F_{t+1} = S\,\frac{1 + F_t}{2} + (1 - S)\,\Theta_{t+1},$$

so the non-identity probabilities $(1 - F_t, 1 - \Theta_t)$ evolve by the matrix

$$A_N = \begin{pmatrix} \frac S2 + \frac{1 - S}{2N} & (1 - S)\bigl(1 - \frac1N\bigr) \\ \frac1{2N} & 1 - \frac1N \end{pmatrix} .$$

Its largest eigenvalue $\lambda_N$ satisfies $N(1 - \lambda_N) \to \frac{1}{2 - S}$ as $N \to \infty$, so the
[eigenvalue effective size](effective-population-size-definitions.md) is

$$N_e = \frac{1}{2(1 - \lambda_N)} = N \Bigl(1 - \frac S2\Bigr) (1 + o(1)) = \frac{N}{1 + F^*}(1 + o(1)), \qquad F^* = \frac{S}{2 - S},$$

where $F^*$ is the equilibrium [inbreeding coefficient under partial selfing](../inbreeding-and-regular-systems-of-mating/inbreeding-under-partial-selfing.md) in an infinite population. With
$S = 0$ this is $N_e = N$. The limit follows from first-order perturbation of the eigenvalue $1$ of $A_\infty$, whose
left eigenvector is $(0, 1)$ and right eigenvector $(2(1 - S), 2 - S)$.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](effective-population-size-definitions.md)

## Proof depends on

- [Inbreeding coefficient under partial self-fertilization](../inbreeding-and-regular-systems-of-mating/inbreeding-under-partial-selfing.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.6 (the recursion method with non-identity probabilities $h_t$ within and $k_t$ between individuals, used there for a population in which selfing is not allowed). The partial-selfing recursion and its eigenvalue are derived above.
