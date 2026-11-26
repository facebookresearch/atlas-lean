# Mean-square error of a vector sample mean without replacement

Let $X_i \in \mathbb R^d$ be fixed for each label $i \in I$, where $I$ is
finite with $|I|=N$. Fix an integer $1\le k\le N$ and draw a subset $S$ of
$I$ uniformly among the $\binom Nk$ subsets of size $k$. Distinct labels may
have equal values. With the Euclidean norm, set

$$
\bar X=\frac{1}{N}\sum_{i\in I} X_i,
\qquad
\bar X_S=\frac{1}{k}\sum_{i\in S} X_i,
\qquad
\sigma_N^2=\frac{1}{N}\sum_{i\in I}\|X_i-\bar X\|^2.
$$

The expectation $\mathbb E_k$ of the squared Euclidean deviation (the sum
of squared coordinate deviations) is

$$
\mathbb E_k[\|\bar X_S-\bar X\|^2]
=
\begin{cases}
0 & \text{if } k=N,\\
\dfrac{N-k}{k(N-1)}\,\sigma_N^2 & \text{if } k<N.
\end{cases}
$$

In a census ($k=N$), $S=I$ with probability one, so the deviation is zero.
This includes $N=k=1$ without evaluating the fraction with $N-1$ in its
denominator.

## Proof

For $1\le k<N$, let $S_r^2$ be the population variance of coordinate $r$
with divisor $N-1$. The
[scalar sample-mean variance identity](../../../Probability/statistical-estimation/finite-population-survey-sampling/rand-exp-sq-sample-mean-sub-pop-mean.md)
gives

$$
\mathbb E_k[((\bar X_S)_r-(\bar X)_r)^2]
= (1-k/N)\,S_r^2/k.
$$

Finite expectation commutes with the sum over coordinates. The two
variance conventions give $\sum_r S_r^2 = \frac{N}{N-1}\sigma_N^2$.
Summing the coordinate identity and substituting this relation gives the
factor in (22).

## Sources

- Konstantin Mishchenko, Ahmed Khaled and Peter Richtárik,
  [*Random Reshuffling: Simple Analysis with Vast Improvements*](https://arxiv.org/pdf/2006.05988v3#page=18),
  arXiv:2006.05988v3, §7, p. 18, Lemma 1, second identity in (22), with the
  singleton census stated separately.
