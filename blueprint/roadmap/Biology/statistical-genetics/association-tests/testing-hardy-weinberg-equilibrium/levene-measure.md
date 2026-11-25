# Levene's law of the heterozygote count

For natural numbers $N$ and $n_A$, Levene's law is the measure on $\mathbb{N}$

$$\lambda_{N, n_A} = \sum_{j = 0}^{n_A} L(N, n_A, j)\, \delta_j,$$

with the
[Levene probabilities](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/levene-prob.md)
$L(N, n_A, j)$ of $j$ heterozygotes among $N$ individuals carrying $n_A$ copies of $A$ (these are
nonnegative). It is supported on $\{0, \dots, n_A\}$. It is a probability measure when $n_A \le 2N$;
for $n_A > 2N$ every Levene probability is $0$ and it is the zero measure.
