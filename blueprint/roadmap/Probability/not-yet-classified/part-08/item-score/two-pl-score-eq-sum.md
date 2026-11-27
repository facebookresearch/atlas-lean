# Score of the two-parameter logistic model

For finitely many items $j$ with discriminations $a_j$ and difficulties $b_j$, let the two-parameter logistic model give binary responses with success probabilities $p_j(\theta) = \sigma\big(a_j(\theta - b_j)\big)$, $\sigma$ the logistic sigmoid, independent across items. For every ability $\theta$ and every response pattern $Y$, the score $\frac{d}{d\theta} \log P_\theta(Y)$ equals

$$\sum_j a_j\big(Y_j - p_j(\theta)\big),$$

with $Y_j \in \{0, 1\}$.
