# Allele loss and extinction in a neutral clonal Galton–Watson population

Let $N,k$ be integers with $0<k<N$. Start $k$ haploid individuals of type
$A$ and $N-k$ of type$a$. Every individual independently produces offspring
with the same law $\nu$ on $\mathbb N$, irrespective of type; every child
inherits its parent's type. There is no mutation, mating or selection.
Let $q$ be the [extinction probability](../../Probability/branching-processes/galton-watson-process/extinction-prob.md)
of one founder's line. Define $\tau_A=\inf\{n:Z_n^A=0\}$ and
$\tau_E=\inf\{n:Z_n^A+Z_n^a=0\}$, with empty infimum infinity.
Then $\tau_A\le\tau_E$ and

$$\mathbb P(\tau_A<\infty)=q^k,\qquad
 \mathbb P(\tau_E<\infty)=q^N,\qquad
 \mathbb P(\tau_A<\infty,\ \tau_E=\infty)=q^k-q^N.$$

The allele-loss probability exceeds the extinction probability exactly
when $0<q<1$. When $q=0$ both are zero, and when $q=1$ both are one.
For a law other than $\delta_1$, mean offspring at most one implies
$q=1$ by the [extinction criterion](../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md).
The degenerate one-child law has $q=0$.

The formula for loss of every type in a designated set is $q^j$, where
$j>0$ is the number of founders carrying one of those types in an otherwise
neutral clonal multitype version. This labels a genetic-loss event; it does
not by itself identify loss of adaptive potential, which needs an explicit
functional or environmental meaning for the designated types.

## Depends on

- [Galton–Watson extinction probability](../../Probability/branching-processes/galton-watson-process/extinction-prob.md)

## Proof depends on

- [Galton–Watson extinction criterion](../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Expansion

Founder descendant trees are independent. All $k$ type-$A$ lines die with
probability $q^k$, and all $N$ lines die with probability $q^N$.
Population extinction is a subset of allele loss, giving the difference
formula. Once the whole population has vanished its type-$A$ count has
vanished, which proves the pathwise time inequality. With $0<k<N$,
$q^k>q^N$ is equivalent to $0<q<1$. No comparison of finite expected loss
times is inferred from these event probabilities.

## Sources

- R. Lande, "Genetics and demography in biological conservation", Science 241 (1988), 1455--1460, <https://doi.org/10.1126/science.3420403>, abstract (distinct demographic and genetic effects). The neutral clonal branching model and formulas are independently derived here; genetic feedback on demography and future adaptability remain separate models.
