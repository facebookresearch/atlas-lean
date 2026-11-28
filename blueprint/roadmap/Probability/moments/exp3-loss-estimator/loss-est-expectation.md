# Loss Est expectation

**Unbiasedness.** Let $n \in \mathbb{N}$, let $p, l : \{0, \dots, n-1\} \to \mathbb{R}$ be weights and losses, and let $\hat{l}_{j,i}$ be the EXP3 estimator, equal to $l_i / p_i$ if $j = i$ and $0$ otherwise. For every arm $i$ with $p_i \ne 0$,

$$\sum_{j=0}^{n-1} p_j \, \hat{l}_{j,i} = l_i.$$

When $p$ is the sampling distribution, the left side is the expectation of the estimator for arm $i$.
