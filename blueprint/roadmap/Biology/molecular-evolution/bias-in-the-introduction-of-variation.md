# Successful-origin weights in an independently marked Poisson model

Let $N,k\ge1$ be integers, $\mu_i\ge0$ and $\pi_i\in[0,1]$ for
$i=1,\ldots,k$, with $\sum_i\mu_i\pi_i>0$. Origins of type $i$ form
independent Poisson processes of rates $N\mu_i$. Give each origin an
independent Bernoulli($\pi_i$) success mark, independent of all arrival
processes and other marks. This is an idealized origin model: the marks do
not specify durations of fixation or guarantee nonoverlapping mutant fates.

The successful-origin processes are independent Poisson processes with
rates $\lambda_i=N\mu_i\pi_i$. A first successful origin exists almost
surely, there is almost surely no tie, and its type has probability

$$P_i=\frac{\lambda_i}{\sum_j\lambda_j}
     =\frac{\mu_i\pi_i}{\sum_j\mu_j\pi_j}.$$

For positive competing rates, $P_i/P_j=(\mu_i/\mu_j)(\pi_i/\pi_j)$.
Multiplying all mutation rates by a common positive factor leaves the winner
probabilities unchanged. This separates the effects of mutation supply and
success probability within this model; it does not identify the first
successful origin with the first physical fixation in an arbitrary population.

## Expansion

For a time interval of length $t$, conditional binomial marking of a
Poisson($N\mu_i t$) count gives probability-generating function
$\exp(N\mu_i\pi_i t(z-1))$. Independence of disjoint increments and of
types follows from independent arrivals and marks. The first successful
time for type $i$ has survival probability $e^{-\lambda_i t}$ (is infinite
if $\lambda_i=0$), and
$P_i=\int_0^\infty\lambda_i e^{-(\sum_j\lambda_j)t}\,dt$.

For the connection to a weak-mutation fixation-flux model at a fixed
resident genotype $g$, take a finite genotype set, positive fitness $f$,
$\mu_h=\mu m(g,h)$ and
$\pi_h=\varphi_1(f(h)/f(g))$, the [one-copy Moran fixation probability](../population-genetics/moran-model/moran-fixation.md).
With a constant total Moran event rate $N$, the candidate physical rates are
$N\mu m(g,h)\varphi_1(f(h)/f(g))$; under time acceleration
$t\mapsto t/(N\mu)$ they become $m(g,h)\varphi_1(f(h)/f(g))$.
An event clock proportional to resident fitness would instead insert
$f(g)$ and is not used here. For $N=1$, equal fitness $f=2$ and a unique
mutational destination, these physical and accelerated rates are $\mu$ and
$1$, not $2\mu$ and $2$.

A reversible stationary law for the resident-by-resident fixation-flux
chain additionally uses symmetric mutation and the Moran fixation-ratio
identity. Justification from a population with mutation also in transient
polymorphic states needs a separate weak-mutation limit for a specified
last-fixed-type or trace process. Neither reversibility nor that convergence
is supplied by independent thinning; finite-rate Poisson arrivals alone do
not make positive-duration mutant fates disjoint.

## Background

- [Moran fixation probability](../population-genetics/moran-model/moran-fixation.md)

## Sources

- L. Y. Yampolsky and A. Stoltzfus, "Bias in the introduction of variation as an orienting factor in evolution", Evolution & Development 3 (2001), 73–83, <https://doi.org/10.1046/j.1525-142x.2001.003002073.x>, abstract (mutation bias in introducing novelty).
- A. Stoltzfus and D. M. McCandlish, "Mutational biases influence parallel adaptation", Molecular Biology and Evolution 34 (2017), 2163–2172, <https://doi.org/10.1093/molbev/msx180>, Introduction (rare adaptive origins and the first-come, first-served approximation). The exact marked-process calculation is derived above.
