# Test information of the two-parameter logistic model as a sum over items

Let $I$ be a finite set of items, let $a, b \in \mathbb{R}^I$ be discriminations and difficulties, and let $\sigma(u) = 1/(1 + e^{-u})$ be the logistic function. For an ability $t \in \mathbb{R}$ and a response pattern $Y \in \{0, 1\}^I$, let

$$
p_t(Y) = \prod_{i \in I} \sigma\big(a_i (t - b_i)\big)^{Y_i}\,\big(1 - \sigma(a_i (t - b_i))\big)^{1 - Y_i}
$$

be the probability of $Y$ under the [two-parameter logistic model](../../../statistical-estimation/item-response-models/two-parameter-logistic-model.md) at ability $t$.

Fix $\theta \in \mathbb{R}$. Let $\mathbb{P}_\theta$ be the [measure with density](../../../statistical-estimation/fisher-information-and-the-cram-r-rao-bound/law-of.md) $p_\theta$ with respect to counting measure on $\{0, 1\}^I$, and let $s_\theta(Y) = \frac{d}{dt} \log p_t(Y) \big|_{t = \theta}$ be the score. The vector Fisher information at $\theta$, with the real line as parameter space, is the linear map $\mathcal{I}(\theta) : \mathbb{R} \to \mathbb{R}$ given by the Bochner integral $\mathcal{I}(\theta) = \int s_\theta(Y)\, s_\theta(Y)^{\top}\, d\mathbb{P}_\theta(Y)$ of the rank-one maps $v \mapsto s_\theta(Y)\,v\,s_\theta(Y)$; its quadratic form at $1$ is the number $\langle \mathcal{I}(\theta) 1, 1 \rangle = \mathcal{I}(\theta)(1)$.

For all $a$, $b$ and $\theta$, the quadratic form at $1$ of the vector Fisher information is the test information

$$
\langle \mathcal{I}(\theta) 1, 1 \rangle = \sum_{j \in I} a_j^2\, \sigma\big(a_j (\theta - b_j)\big)\,\Big(1 - \sigma\big(a_j (\theta - b_j)\big)\Big).
$$

A sum over an empty set of items is $0$.
