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

If $k=N$, the sole sample is $I$ and its mean is $\bar X$, including when
$N=1$. Otherwise fix a coordinate $r$ and write $y_i=(X_i)_r$. In the
complete-randomization unbiasedness identity, take the treated set to be $S$,
the treated outcomes to be $y_i$ and the control outcomes to be zero. The
scalar difference in means is then $(\bar X_S)_r$, and the average treatment
effect is $(\bar X)_r$. Applying the identity in every coordinate gives the
vector equality. The exact real-valued special case (including the census) is
[`randExp_sampleMean`](https://github.com/facebookresearch/atlas-lean/blob/bb9ed90b40cede6b893a6a05435969113b3ec58b/MathlibExt/Probability/Sampling/SimpleRandomSampling.lean#L109-L123).

## Depends on

- [Expectation under complete randomization](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp.md) for real-valued coordinates.

## Proof depends on

- [Unbiasedness of the difference in means under complete randomization](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp-diff-in-means.md) when $k<N$.

## Sources

- Konstantin Mishchenko, Ahmed Khaled and Peter Richtárik,
  [*Random Reshuffling: Simple Analysis with Vast Improvements*](https://arxiv.org/pdf/2006.05988v3#page=18),
  arXiv:2006.05988v3, §7, p. 18, Lemma 1, first identity in (22).
