# Mean of a vector sample without replacement

Let $X_i \in \mathbb R^d$ be fixed for each label $i \in I$, where $I$ is
finite with $|I|=N$. Fix an integer $1\le k\le N$ and draw a subset $S$ of
$I$ uniformly among the $\binom Nk$ subsets of size $k$. Distinct labels may
have equal values. Set

$$
\bar X = \frac{1}{N}\sum_{i\in I} X_i,
\qquad
\bar X_S = \frac{1}{k}\sum_{i\in S} X_i.
$$

Write $\mathbb E_k$ for the finite average over these subsets, applying the
real-valued expectation under complete randomization to each coordinate. Then

$$
\mathbb E_k[\bar X_S] = \bar X.
$$

## Proof

For each coordinate $r$, apply the
[scalar sample-mean identity](../../../Probability/statistical-estimation/finite-population-survey-sampling/rand-exp-sample-mean.md)
to the values $y_i=(X_i)_r$. The expectation of that coordinate of
$\bar X_S$ is the corresponding coordinate of $\bar X$. In a census
($k=N$), including $N=1$, the sole sample is $I$.

## Sources

- Konstantin Mishchenko, Ahmed Khaled and Peter Richtárik,
  [*Random Reshuffling: Simple Analysis with Vast Improvements*](https://arxiv.org/pdf/2006.05988v3#page=18),
  arXiv:2006.05988v3, §7, p. 18, Lemma 1, first identity in (22).
