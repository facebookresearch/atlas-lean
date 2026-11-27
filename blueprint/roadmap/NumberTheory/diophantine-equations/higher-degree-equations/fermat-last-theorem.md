# Fermat's Last Theorem

For every natural number $n\ge 3$ and all positive natural numbers $a,b,c$,

$$
a^n+b^n\ne c^n.
$$

Equivalently, the equation has no solution in nonzero natural numbers, since a natural number is positive exactly when it is nonzero. This is the proposition `FermatLastTheorem` in Mathlib.

## Proof depends on

- [Fermat’s equation at primes at least five](fermat-prime-exponents/fermat-equation-at-primes-at-least-five.md)
- [Vanishing of weight-two cusp forms at level two](../../modular-forms-q-series/modular-forms/weight-two-cusp-forms-on-2/s2-gamma0-2-eq-zero.md)

## Proof outline

Use the reduction from arbitrary exponents to exponent four and odd prime exponents. The cases of exponent three and four are classical; for prime $p\ge5$, the cited proof normalizes a counterexample to a Frey package. Track its mod-$p$ irreducibility, modularity in the sense of equality of traces at good primes, and level lowering to a nonzero weight-two cusp form of level two as separate prerequisites. The local proposition does not depend on the choice of proof route.

## Sources

- Andrew Wiles, *Modular elliptic curves and Fermat's Last Theorem*, Annals of Mathematics 141 (1995), 443–551; Richard Taylor and Andrew Wiles, *Ring-theoretic properties of certain Hecke algebras*, ibid., 553–572.
- Anthropic's formalization: [the positive-natural statement](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_fermat_last_theorem.lean#L128), [the Mathlib form](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/FinalCheck.lean#L7), and [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
