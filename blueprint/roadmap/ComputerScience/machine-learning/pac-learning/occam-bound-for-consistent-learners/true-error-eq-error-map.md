# Bridge from the true error to the error under the labelled distribution

If the target $c$ is measurable and the disagreement set $\{(x, y) : h(x) \ne y\}$ is measurable,
then the true error of $h$ against $c$ under $\mu$ equals the 0-1 error of $h$ under the
pushforward $\mu \circ (x \mapsto (x, c(x)))^{-1}$ of $\mu$ along the graph of $c$:

$$\operatorname{err}_\mu(h) = \operatorname{error}_{\mu_c}(h), \qquad \mu_c = (x \mapsto (x, c(x)))_* \mu .$$
