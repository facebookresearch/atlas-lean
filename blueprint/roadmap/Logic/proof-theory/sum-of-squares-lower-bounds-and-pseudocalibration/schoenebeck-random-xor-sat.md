# Grigoriev–Schoenebeck: linear-degree SoS lower bounds for random 3-XOR and 3-SAT

For every $\varepsilon > 0$ there is $\Delta_0(\varepsilon)$ such that for every constant $\Delta \ge \Delta_0(\varepsilon)$ there is $c = c(\Delta) > 0$ such that, with high probability, a random $3$-XOR instance (respectively random $3$-SAT instance) with $n$ variables and $\Delta n$ constraints has optimum at most $\frac{1}{2} + \varepsilon$ (respectively $\frac{7}{8} + \varepsilon$), but the degree-$c n$ sum-of-squares relaxation assigns it value $1$: there is a degree-$cn$ pseudo-expectation satisfying all constraints exactly.

## Proof sketch

Random sparse $3$-uniform hypergraphs are boundary expanders: every set of $s \le cn$ constraints has many variables appearing in exactly one of them. Expansion implies that no derivation of width below $cn$ derives a contradiction from the XOR constraints by Gaussian elimination, and a linear-algebraic construction defines a pseudo-expectation consistent with every constraint that is a symmetric function of derived parities of width less than $cn$; positivity follows from writing it as a mixture over consistent assignments on each small closed set. For $3$-SAT, a satisfying $3$-XOR pseudo-solution with the correct literal signs satisfies every $3$-SAT clause.

## Depends on

- [Refutation of random constraint satisfaction problems](random-csp-refutation.md)
- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)

## Sources

- D. Grigoriev, "Linear lower bound on degrees of Positivstellensatz calculus proofs for the parity", Theoretical Computer Science 259 (2001) 613-622.
- G. Schoenebeck, "Linear level Lasserre lower bounds for certain k-CSPs", FOCS (2008).
