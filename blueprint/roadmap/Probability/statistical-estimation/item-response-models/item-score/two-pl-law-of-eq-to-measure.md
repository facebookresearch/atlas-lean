# Law of the two-parameter logistic response pattern

Let $I$ be a finite set of items, let $a, b \in \mathbb{R}^I$ be discriminations and difficulties, and let $\sigma(u) = 1/(1 + e^{-u})$ be the logistic function. For an ability $t \in \mathbb{R}$ and a response pattern $Y \in \{0, 1\}^I$, let

$$
p_t(Y) = \prod_{i \in I} \sigma\big(a_i (t - b_i)\big)^{Y_i}\,\big(1 - \sigma(a_i (t - b_i))\big)^{1 - Y_i}
$$

be the probability of $Y$ under the [two-parameter logistic model](../../../statistical-estimation/item-response-models/two-parameter-logistic-model.md) at ability $t$.

Fix $\theta \in \mathbb{R}$. The [measure with density](../../../statistical-estimation/fisher-information-and-the-cram-r-rao-bound/law-of.md) $p_\theta$ with respect to counting measure on $\{0, 1\}^I$, that is $E \mapsto \sum_{Y \in E} p_\theta(Y)$, equals the probability distribution of the response pattern under the two-parameter logistic model at ability $\theta$, the measure assigning mass $p_\theta(Y)$ to each pattern $Y$.
