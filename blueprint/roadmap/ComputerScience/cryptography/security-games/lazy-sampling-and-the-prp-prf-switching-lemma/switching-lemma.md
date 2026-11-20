# The PRP/PRF switching lemma

Let $D$ be a finite nonempty set with $N$ elements and $c$ an adaptive distinguisher with oracle
access to a function $D \to D$ that makes at most $q$ queries along every path, repeated queries
included. Its distinguishing advantage between a uniformly random function $f : D \to D$ and a
uniformly random permutation $\pi$ of $D$, each drawn once and then queried, is at most
$$1 - \frac{N(N - 1) \cdots (N - q + 1)}{N^q},$$
the probability that $q$ independent uniform samples from $D$ are not all distinct (Katz and Lindell,
Section 3.5.1, the step behind Proposition 3.27; Bellare and Rogaway, Lemma 1).
