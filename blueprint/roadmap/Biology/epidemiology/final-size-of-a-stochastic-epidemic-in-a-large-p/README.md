# Final size of a stochastic epidemic in a large population

A generation-based SIR epidemic in a population of $N$ individuals, with a set $S_0$ of
$\#S_0$ initially susceptible individuals, is started by one index case; the $i$-th infective of
generation $n$ makes $\xi_{n,i}$ contacts and contact number $j$ goes to individual $U_j$. Suppose
the offspring numbers are i.i.d. with law $\nu$, a probability measure on $\mathbb{N}$ with
$\int x^2 \, d\nu(x) < \infty$ and mean $R_0 = \int x \, d\nu(x) > 1$, the targets are i.i.d.
uniform and independent of the offspring numbers, $N \to \infty$ and $(N - \#S_0)/N \to 0$. Then
the fraction $F/N$ of the population ultimately infected satisfies $P(F/N < \delta) \to q$ and
$P(|F/N - \tau| < \delta) \to 1 - q$ for every $0 < \delta < \tau$, where $q$ is the extinction
probability of the Galton–Watson process with offspring law $\nu$ and $\tau$ is the unique positive
root of $1 - \tau = e^{-R_0 \tau}$.

## Deterministic final size

- [After an empty generation the epidemic state no longer changes](epi-eq-of-epi-size-eq-zero.md)
- [The epidemic state is constant from generation $\#S_0 + 1$ on](epi-eq-epi-card-add-one.md)
- [Contacts made before generation n sum the infectives' contact numbers](epi-snd-eq-sum.md)
- [Total number of contacts made during the epidemic](total-contacts.md)
- [Final size: the number of individuals ever infected](final-size.md)
- [The final size is the sum of the generation sizes after the index case](final-size-eq-sum.md)
- [The final size is at most the number of initial susceptibles](final-size-le-card.md)
- [Infectives of all generations, index case included, number F + 1](sum-epi-size-eq-final-size-add-one.md)
- [Total contacts are the sum of the contact numbers of all infectives](total-contacts-eq-sum.md)
- [If generation $n$ is empty, then $F < I_0 + \cdots + I_{n-1}$](final-size-lt-of-epi-size-eq-zero.md)

## The final-size equation

- [The final-size function $1 - e^{-Rx} - x$](final-size-gap.md)
- [For $R > 1$ the final-size equation has a root in $(0, 1)$](exists-final-size-gap-eq-zero.md)
- [For $R > 0$ the final-size equation has at most one positive root](eq-of-final-size-gap-eq-zero.md)
- [Positive root $\tau(R)$ of the final-size equation, $0$ if $R \le 1$](final-size-root.md)
- [For $R > 1$, $\tau(R)$ solves the final-size equation](one-sub-final-size-root.md)
- [For $R > 1$, every positive final-size root equals $\tau(R)$](eq-final-size-root.md)
- [For $R > 1$, near-roots in the unit interval lie near $0$ or $\tau(R)$](exists-pos-forall-abs-final-size-gap-le.md)

## Configurations, measurability and independence

- [With fixed targets, earlier offspring numbers determine generation n](epi-congr.md)
- [Configurations: offspring numbers and contact targets](config.md)
- [Epidemic state of a configuration at generation n](epi-of.md)
- [Final-size epidemic model: targets independent of offspring numbers](is-final-size-epidemic.md)
- [Configuration of the model at an outcome](config-2.md)
- [Configuration at an outcome with one offspring number set to zero](config-without.md)
- [One offspring number is independent of the rest of the configuration](indep-fun-config-without.md)
- [The integral of φ(rest of configuration) · f(one offspring) factorizes](integral-mul-offspring.md)

## The centered contact count

- [Number of infectives of generations 0 to n of a configuration](cum-of.md)
- [Gate: an infective with at most L infectives up to its generation](gate.md)
- [Contacts of generations within a cap L, centered at m per infective](trunc-dev.md)
- [The gates add up to at most L](sum-gate-le.md)
- [Once $F + 1 \le L$, the centered contact count is $C - m(F + 1)$](trunc-dev-eq.md)

## Second-moment bound for the contact count

- [Real-valued mean of an offspring law](offspring-mean.md)
- [Real-valued variance of an offspring law](offspring-var.md)
- [With a finite second moment, the extended mean is the real mean](mean-eq-of-real-offspring-mean.md)
- [The centered contact count has second moment at most $\sigma^2 L$](integral-trunc-dev-sq-le.md)
- [Chebyshev bound for the centered contact count](measure-real-le-abs-trunc-dev.md)

## Occupancy bounds for the contact targets

- [Markov's inequality for the square of a function](measure-real-le-abs-le.md)
- [Concentration of a count of pairwise non-positively correlated events](measure-real-le-abs-sum-indicator-sub.md)
- [Number of hits among the first c contacts](hits.md)
- [Number of the first m contacts that go outside $S_0$](outside-contacts.md)
- [Number of the first m contacts to an individual contacted before](repeat-contacts.md)
- [Hits and never-contacted initial susceptibles together number $\#S_0$](hits-add-card-filter.md)
- [Contacts that do not hit go outside $S_0$ or repeat a target](sub-hits-le.md)
- [Probability that given contacts all reach a given set of individuals](measure-real-forall-mem.md)
- [Chebyshev bound for the number of hits among the first c contacts](measure-real-le-abs-hits-sub.md)
- [Chebyshev bound for the number of contacts outside $S_0$](measure-real-le-abs-outside-contacts-sub.md)
- [Markov bound for the repeated contacts among the first m](measure-real-le-repeat-contacts.md)

## Real-analysis helpers

- [For $n \ge 1$, $(1 - 1/n)^c$ is within $c/n^2$ of $e^{-c/n}$](abs-one-sub-inv-pow-sub-exp-le.md)
- [For s ≤ n, n ≥ 1, s(1 − (1 − 1/n)^c) = n(1 − e^(−c/n)) ± (n − s + c/n)](abs-mean-hits-sub-le.md)
- [Monotone H θ-close to f of slope ≤ 1 on a d-grid is (θ + d)-close](abs-sub-le-of-grid.md)

## Small outbreaks

- [If the first K contacts hit and F < K, the branching process dies out](exists-bp-size-eq-zero-of-final-size-lt.md)
- [A final size between 2ʲ and 2ʲ⁺¹ needs deviating or wasted contacts](dyadic-case-split.md)
- [For m > 1, a bound on the probability that 2ʲ ≤ F < 2ʲ⁺¹ and F < δN](measure-real-dyadic-le.md)

## The model is satisfiable

- [The coordinates of the canonical product space form a final-size model](is-final-size-epidemic-canonical.md)

## Large-population limits

- [Uniform law of large numbers for the hits among up to K N contacts](tendsto-measure-real-exists-abs-hits-sub.md)
- [The centered contact count with cap N + 1 is o(N) in probability](tendsto-measure-real-le-abs-trunc-dev.md)
- [For R₀ > 1 and few immune, F/N is near 0 or τ with high probability](tendsto-measure-real-final-size-far.md)
- [R₀ > 1, few immune, θ > 0: a δ₀ > 0 has P(F < δ₀N) ≤ q + θ eventually as N → ∞](exists-eventually-measure-real-final-siz.md)
- [For all δ, θ > 0, P(F < δN) ≥ q − θ eventually as N → ∞](eventually-le-measure-real-final-size-lt.md)
- [With R₀ > 1, 0 < δ < τ and few immune, P(F/N < δ) tends to q](tendsto-measure-real-final-size-div-lt.md)
- [For R₀ > 1, 0 < δ < τ, few immune: P(F/N within δ of τ) tends to 1 − q](tendsto-measure-real-abs-final-size-div.md)
