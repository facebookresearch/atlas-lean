# Branching of competing first-order decay channels

When an excited state decays by several first-order channels at once, the share of decays that go through one channel is its rate constant times the lifetime. The yield is counted per excited state prepared, which is not the same denominator as the photon-based yield.

Let an excited state be prepared with population $c(0) > 0$ and decay by first-order channels with rate constants $k_1, \dots, k_m \ge 0$ whose sum is positive, and let $\tau = 1/\sum_i k_i$. With no process repopulating the state, the number of events of channel $j$ per prepared excited state is

$$
\Phi_j = \frac{k_j}{\sum_{i=1}^{m} k_i} = k_j \tau .
$$

Hence $0 \le \Phi_j \le 1$ and $\sum_j \Phi_j = 1$; $\Phi_j > 0$ exactly when $k_j > 0$, and $\Phi_j = 1$ exactly when every other rate constant vanishes, which for a list of strictly positive rate constants happens only when $m = 1$. When the radiative rate constants sum to $k_{\mathrm{r}} > 0$ the radiative yield is $\Phi_{\mathrm{r}} = k_{\mathrm{r}}\tau = \tau/\tau_{0}$ with $\tau_{0} = 1/k_{\mathrm{r}}$; for $k_{\mathrm{r}} = 0$ the radiative lifetime is not finite and the quotient form does not apply.

Three hypotheses carry the identity: every channel is first order in the state, the channels act in parallel on one state, and nothing repopulates it. Repopulation invalidates the single-exponential argument, as in delayed fluorescence, where a triplet reservoir feeds the emitting singlet; what the yield then becomes depends on the full kinetic scheme, so no general comparison with the one-pass value is claimed here. Relating $\Phi_j$ to a yield per absorbed photon requires the yield with which the state is formed.

## Depends on

- [Lifetime of an excited state](excited-state-lifetime.md)
- [Quantum yield of a photophysical process](quantum-yield-of-a-photophysical-process.md)

## Proof depends on

- [Integrated first-order rate law](../../chemical-kinetics/rate-laws/first-order-sol.md)

## Expansion

With $c(t) = c(0)\exp(-t/\tau)$ the events of channel $j$ per prepared state are $\int_0^{\infty} k_j c(t)\,\mathrm{d}t / c(0) = k_j\tau$, using $\int_0^{\infty}\exp(-t/\tau)\mathrm{d}t = \tau$ and $c(0) > 0$. The bounds and the normalization follow from $0 \le k_j \le \sum_i k_i$ and summation over $j$; the equality cases are read off the same inequality.

## Context

Undergraduate. The identity behind photophysical rate analysis in this chapter: a measured yield and lifetime fix the rate constant of a channel, which is how radiative and non-radiative rates of a designed emitter are extracted.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entries “lifetime, s” (p. 363) and “quantum yield, $\Phi$” (pp. 406–407), together with the “radiative lifetime, s” entry (p. 411); the identity is derived from those definitions for a single prepared state, as the expansion shows.
