# Two primes in infinitely many translates of the explicit forty shifts

Let $H$ be the set of entries of the explicit forty-shift tuple of diameter 186. There are infinitely many natural numbers $n$ such that $\#\{h\in H : n+h\text{ is prime}\}\ge 2$. Either the set of offsets or their injective indexing can be used for the count. Both primes are in the same translate; this statement does not require them to be consecutive.

The cited proof is conditional on three unproved analytic inputs: the normalized rank-three Kloosterman bound, a rank-two Kloosterman correlation bound, and the physical trial-integral bounds.

## Depends on

- [The explicit 40-tuple for the gap bound 186](tuple186.md)

## Proof depends on

- [Two primes in infinitely many translates of an admissible 40-tuple](openai2026-dhl.md)
- [The explicit 40-tuple is admissible](tuple186-admissible.md)
- [The explicit 40-tuple has distinct entries](tuple186-injective.md)
- [The entries of the explicit 40-tuple lie between 0 and 186](tuple186-bounds.md)

## Proof outline

Specialize the general 40-tuple result once available; identify the image of the explicit injective tuple with the source finset and use nonnegativity of its entries to identify integer-plus-natural primality with natural primality. Alternatively discharge the three analytic inputs before transferring the cited conditional proof.

## Sources

- [Pinned source: `infinite_two_prime_translates_admissibleTuple`](https://github.com/openai/PrimeGaps186/blob/61340d0b74163003b32756bb16e91d9209a5e330/Challenge.lean#L957-L959)
