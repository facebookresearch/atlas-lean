# Normalized composite score

In a [composite-score model](composite-model.md) with prior $\pi$, the normalized composite score of an observation $x = (x_1, \dots, x_k)$ is

$$\mathrm{Post}(x) = \frac{\pi \prod_i s_i(x_i)}{\pi \prod_i s_i(x_i) + (1 - \pi) \prod_i n_i(x_i)}.$$

When the score functions are normalized densities it is the posterior probability of selection given $x$.
