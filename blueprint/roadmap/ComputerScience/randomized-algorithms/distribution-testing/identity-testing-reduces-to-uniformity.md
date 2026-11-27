# Goldreich: identity testing reduces to uniformity testing

For every fixed distribution $q$ on $n$ points there is a randomized map $\Phi_q$ from the $n$ points to a domain of $6n$ points such that $\Phi_q$ sends $q$ to the uniform distribution and maps any $p$ with $d_{TV}(p, q) \ge \varepsilon$ to a distribution at total variation distance at least $\varepsilon/3$ from uniform. Consequently identity testing to $q$ with proximity $\varepsilon$ reduces to uniformity testing on $6n$ points with proximity $\varepsilon/3$ and the same number of samples; with the collision tester this gives $O(\sqrt n/\varepsilon^2)$ samples.

## Proof sketch

First mix each sample with a uniform draw with probability $1/2$, so every mass of the target is at least $1/(2n)$; then round masses down to multiples of $1/(6n)$ ("grains") and map each point uniformly into a block of size proportional to its rounded mass, with the remaining mass sent to dedicated points. Distances shrink by at most a constant factor at each step.

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Proof depends on

- [The collision tester for uniformity](collision-tester-for-uniformity.md)

## Sources

- O. Goldreich, "The Uniform Distribution is Complete with Respect to Testing Identity to a Fixed Distribution", ECCC technical report TR16-015, 2016, Theorem 1.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
