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

Under this uniform sampling law, the real expectation $\mathbb E_k$ of the
squared deviation is

$$
\mathbb E_k[\|\bar X_S-\bar X\|^2]
=
\begin{cases}
\dfrac{N-k}{k(N-1)}\,\sigma_N^2 & \text{if } N>1,\\
0 & \text{if } N=k=1.
\end{cases}
$$

In a census ($k=N$), $S=I$ with probability one, so the deviation is zero.
In particular, the singleton case does not evaluate the fraction with
$N-1$ in its denominator.

## Proof

The census is immediate as above. For $1\le k<N$, fix a coordinate $r$ and
write $y_i=(X_i)_r$. Let $S_r^2$ be the population variance of this coordinate
with divisor $N-1$. Apply the complete-randomization variance formula with
treated set $S$, treated outcomes $y_i$ and control outcomes zero. The
difference in means and its target are $(\bar X_S)_r$ and $(\bar X)_r$;
the treated and unit-effect population variances are both $S_r^2$, and the
control population variance is zero. The resulting coordinate formula is

$$
\mathbb E_k[((\bar X_S)_r-(\bar X)_r)^2]
= S_r^2/k - S_r^2/N
= (1-k/N)\,S_r^2/k.
$$

This is the real-valued identity
[`randExp_sq_sampleMean_sub_popMean`](https://github.com/facebookresearch/atlas-lean/blob/bb9ed90b40cede6b893a6a05435969113b3ec58b/MathlibExt/Probability/Sampling/SimpleRandomSampling.lean#L125-L141),
which also includes the census. The squared Euclidean norm is the sum of
squared coordinates, and the finite expectation commutes with this sum.
For $N>1$ the two variance conventions give
$\sum_r S_r^2 = \frac{N}{N-1}\sigma_N^2$. Summing the coordinate identity
and substituting this relation gives the factor in (22).

## Depends on

- [Expectation under complete randomization](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp.md).

## Proof depends on

- [Variance of the difference in means under complete randomization](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp-sq-diff-in-means-sub-ate.md) when $k<N$.
- [Population variance with divisor $N-1$](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/pop-var.md) for the coordinatewise normalization.

## Sources

- Konstantin Mishchenko, Ahmed Khaled and Peter Richtárik,
  [*Random Reshuffling: Simple Analysis with Vast Improvements*](https://arxiv.org/pdf/2006.05988v3#page=18),
  arXiv:2006.05988v3, §7, p. 18, Lemma 1, second identity in (22), with the
  singleton census stated separately.
