# Score, information and the most informative item in the two-parameter logistic model

Let $J$ be a finite nonempty set of items with discriminations $a_j > 0$ and difficulties $b_j$, let $p_j(\theta) = \sigma(a_j(\theta - b_j))$ with $\sigma(x) = 1/(1 + e^{-x})$, and let the responses $(Y_j)_{j \in J}$ be independent given $\theta$ with $P(Y_j = 1 \mid \theta) = p_j(\theta)$, so their law is the product of these Bernoulli laws. The derivative in $\theta$ of the log-likelihood is the score $\sum_j a_j(Y_j - p_j(\theta))$, which has mean $0$ under this product law, and the Fisher information is $I(\theta) = \sum_j a_j^2p_j(\theta)(1 - p_j(\theta)) > 0$, the variance of the score. For any fixed ability value $\hat\theta$ and finite nonempty set $E \subseteq J$ of eligible items, some $j \in E$ maximizes the item information $a_j^2p_j(\hat\theta)(1 - p_j(\hat\theta))$. Here $\hat\theta$ is any fixed value: existence of a maximum-likelihood ability estimate, unbiasedness, asymptotic distributions and confidence statements are not claimed.

## Proof depends on

- [Fisher information is the second moment of the score](../asymptotic-normality-of-maximum-likelihood/integral-score-sq.md): the information is the second moment of the score.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
