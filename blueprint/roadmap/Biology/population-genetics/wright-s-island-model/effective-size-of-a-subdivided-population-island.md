# Effective size of an island-model population

Let $d \ge 2$ demes each hold $2N$ gene copies. Going back one generation, each gene's parental deme is its own with probability $1 - m$
and each other deme with probability $m/(d - 1)$, independently for distinct genes, and it copies a uniform one of the $2N$ copies of
that deme. Two distinct genes have parents in the same deme with probability

$$s_0 = (1 - m)^2 + \frac{m^2}{d - 1} \ \text{(same deme now)}, \qquad s_1 = \frac{2m(1 - m)}{d - 1} + \frac{m^2 (d - 2)}{(d - 1)^2} \ \text{(different demes)},$$

so, with $a = 1/(2N)$, the non-identity probabilities $(h_0, h_1)$ within and between demes evolve by

$$\begin{pmatrix} h_0' \\ h_1' \end{pmatrix} = \begin{pmatrix} s_0(1 - a) & 1 - s_0 \\ s_1(1 - a) & 1 - s_1 \end{pmatrix} \begin{pmatrix} h_0 \\ h_1 \end{pmatrix}.$$

For $0 < m < 1$ its leading eigenvalue $\lambda$ is below $1$, and the [eigenvalue effective size](../effective-population-size/effective-population-size-definitions.md) is $N_e = 1/(2(1 - \lambda))$. Under
perfect mixing, $m = (d - 1)/d$, $s_0 = s_1 = 1/d$ and $N_e = dN$ exactly. As $N \to \infty$ with $M = Nm > 0$ fixed, $N(1 - \lambda) \to x$, the smaller root of

$$x^2 - \Bigl(2M + \frac12 + \frac{2M}{d - 1}\Bigr) x + \frac{M}{d - 1} = 0,$$

so $N_e / (dN) \to 1/(2dx)$, which exceeds $1$, tends to $1$ as $M \to \infty$ and to infinity as $M \to 0$. Within-deme identity at
equilibrium, Wright's [island-model equilibrium](island-equilibrium.md), is a separate quantity.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](../effective-population-size/effective-population-size-definitions.md)

## Related topics

- [Equilibrium $F_{ST}$ of Wright's island model](island-equilibrium.md)

## Sources

- M. C. Whitlock and N. H. Barton, "The effective size of a subdivided population", Genetics 146 (1997), 427–441, <https://doi.org/10.1093/genetics/146.1.427>. The recursion and limit are derived above.
