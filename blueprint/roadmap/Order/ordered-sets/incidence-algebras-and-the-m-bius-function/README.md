# Incidence algebras and the Möbius function

The Möbius function $\mu$ of a locally finite poset is the inverse of its zeta function in the
incidence algebra: $\mu(s, s) = 1$ and $\sum_{s \le u \le t} \mu(s, u) = 0$ for $s < t$. It turns
summation over order ideals into an invertible operation (Möbius inversion), is multiplicative on
products, and equals an alternating count of chains (Philip Hall's theorem), which links it to the
Euler characteristic of the order complex. Stanley, *Enumerative Combinatorics*, vol. 1,
Sections 3.6 to 3.9, develops it in this order.

The pages below build on the incidence algebra, the zeta and Möbius functions, one direction of
Möbius inversion and the product theorem in algebra form.

## Möbius inversion and products

- [Möbius inversion formula](moebius-inversion-iff.md)
- [Möbius inversion formula, dual form](moebius-inversion-dual-iff.md)
- [Product theorem for the Möbius function](mu-prod-apply.md)
- [Möbius function of the poset of finite subsets](mu-finset-of-subset.md)

## Philip Hall's theorem

- [Chains of length $i$ between two elements](chains-between.md)
- [Membership in the chains between two elements](mem-chains-between.md)
- [Number of chains of length $i$ between two elements](chain-count.md)
- [Chains of length zero](chain-count-zero.md)
- [Chains are no longer than the interval](chain-count-eq-zero-of-card-le.md)
- [Removing the last step of a chain](chain-count-succ.md)
- [Philip Hall's theorem](mu-eq-sum-chain-count.md)
- [Philip Hall's theorem, truncated at any bound](mu-eq-sum-chain-count-of-card-le.md)
- [Philip Hall's theorem for a bounded poset](euler-char-eq-sum-chain-count.md)

## Lattices: Weisner and crosscut

- [Weisner's theorem](sum-mu-top-of-inf-eq-bot.md)
- [Crosscut theorem](mu-bot-top-eq-sum-crosscut.md)
- [Crosscut theorem, summed over subsets](mu-bot-top-eq-sum-powerset.md)

## Related topics

- [Möbius algebras and flag vectors](../../../Combinatorics/partially-ordered-sets/m-bius-algebras-and-flag-vectors/README.md):
  the Möbius algebra of a lattice, whose basis $\delta_t$ is built from $\mu$ and which Stanley uses
  to prove Weisner's and the crosscut theorem.
- [Multiplicative functions and mean values](../../../NumberTheory/arithmetic-functions/multiplicative-functions/README.md):
  the classical Möbius function of number theory is $\mu(1, n)$ in the lattice of divisors of $n$, a
  product of chains (Stanley, Example 3.8.4).
