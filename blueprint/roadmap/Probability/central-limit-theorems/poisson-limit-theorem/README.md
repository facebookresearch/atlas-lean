# Poisson limit theorem for binomial laws

For every real $\lambda \ge 0$, the binomial laws $\mathrm{Bin}(n, \lambda/(n + \lambda))$ converge
weakly to the Poisson law with parameter $\lambda$ as $n \to \infty$, as probability measures on
$\mathbb{R}$: $\int f \, d\mathrm{Bin}(n, \lambda/(n + \lambda)) \to \int f \, d\mathrm{Poi}(\lambda)$
for every bounded continuous $f : \mathbb{R} \to \mathbb{R}$.

## Idea

The Poisson law is the law of rare events: many independent trials, each with a small success
probability, and an expected number of successes close to $\lambda$. Here the success probability
$\lambda/(n + \lambda)$ lies in $[0, 1]$ for every $n$, and the mean $n\lambda/(n + \lambda)$ of the
binomial law tends to $\lambda$. One proof compares characteristic functions:
$(1 - p_n + p_n e^{it})^n$ tends to $\exp(\lambda(e^{it} - 1))$, the characteristic function of the
Poisson law, and Lévy's continuity theorem gives weak convergence. The card also contains a more
general analytic statement for triangular arrays: if the success probabilities $p_{n,i} \ge 0$ are
uniformly small and their row sums tend to $\lambda$, then the probability of exactly $j$ successes
tends to $e^{-\lambda} \lambda^j / j!$. The classical form, $\mathrm{Bin}(n, p_n)$ with
$n p_n \to \lambda$, follows from it.

## Statements

- [Poisson convergence in law (binomial approximation)](tendsto-binomial-poisson-approx.md)
- [Binomial law as a probability measure](binomial-prob-measure.md): definition used in the main statement
- [Poisson law as a probability measure](poisson-prob-measure.md): definition used in the main statement
- [Success probability of the binomial approximation to Poisson](poisson-approx-prob.md): definition used in the main statement
- [Binomial approximation to the Poisson law](binomial-poisson-approx.md): definition used in the main statement
- [Mean of the binomial approximation tends to the Poisson rate](tendsto-mul-poisson-approx-prob.md): lemma used in the characteristic-function proof
- [Characteristic function of a binomial law](char-fun-binomial-prob-measure.md): lemma used in the characteristic-function proof
- [Characteristic function of a Poisson law](char-fun-poisson-prob-measure.md): lemma used in the characteristic-function proof
- [Convergence of characteristic functions to the Poisson law](tendsto-char-fun-binomial-poisson-approx.md): lemma used in the proof of the main statement
- [Analytic core of Poisson convergence](elem-symm-poly-tendsto-poisson.md): more general form for triangular arrays with non-identical success probabilities, stated for point masses
- [Chen–Stein Poisson approximation: two moments suffice](chen-stein-poisson-approximation-two-moments-suffice.md): total-variation bound for Poisson approximation of a sum of dependent indicators, reducing to first- and second-order data when the outside-dependence term vanishes

## Background

- [Lévy's continuity theorem](../../characteristic-functions/levy-continuity-theorem/README.md):
  converts convergence of characteristic functions into weak convergence.
