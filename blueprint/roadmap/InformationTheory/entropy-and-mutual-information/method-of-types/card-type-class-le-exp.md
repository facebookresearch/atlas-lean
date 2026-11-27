# Upper bound on the size of a type class

For $n \ge 1$ and an $n$-type with empirical distribution $P$, with the natural logarithm,

$$|T_P| \le e^{nH(P)}, \qquad H(P) = \sum_a -P(a)\log P(a).$$

Proof (Csiszár's): by (II.1) with $Q = P$, $P^n(T_P) = |T_P|\,e^{-nH(P)}$, and $P^n(T_P) \le 1$.
This is the right half of (II.4), exactly as in the source.

## Background

- [Shannon entropy](../shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md): the entropy there
  is in bits; the natural-log entropy $\sum_a -P(a)\log P(a)$ used here is it times $\log 2$.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Lemma II.2, (II.4).
- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Lemma 2.2 (base 2).
