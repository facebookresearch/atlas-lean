# Ornstein's isomorphism theorem

Let $S$ and $S'$ be finite alphabets with probability vectors $p$ and $q$. If the two-sided Bernoulli shifts
on $S^{\mathbb{Z}}$ and $S'^{\mathbb{Z}}$, with product measures $p^{\mathbb{Z}}$ and $q^{\mathbb{Z}}$, have the
same Kolmogorov–Sinai entropy, then they are [isomorphic modulo null sets](is-isomorphic-mod0.md): there are
measure-preserving maps in both directions, inverse to each other almost everywhere, that intertwine the two
[two-sided shifts](../mixing/two-sided-shift.md) almost everywhere.

Together with [invariance under isomorphism modulo null sets](ks-entropy-eq-of-is-isomorphic-mod0.md), entropy
is therefore a complete invariant of invertible Bernoulli schemes, closing the problem that entropy was invented
for. The isomorphism cannot in general be an everywhere conjugacy: the uniform scheme on four letters and the
scheme $(\tfrac12, \tfrac18, \tfrac18, \tfrac18, \tfrac18)$ both have entropy $2 \log 2$, but their shifts have
four and five fixed points. The theorem is about two-sided shifts: one-sided Bernoulli shifts with equal
entropy need not be isomorphic.

## Sources

- Donald Ornstein, *Bernoulli shifts with the same entropy are isomorphic*, Adv. Math. 4 (1970), 337–352,
  DOI 10.1016/0001-8708(70)90029-0.
- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), introduction to Chapter 4 ("Two Bernoulli schemes are measure
  theoretically isomorphic iff their metric entropies are equal") and the notes at the end of Chapter 4.
