# Posterior distribution on hypotheses

Let $H$ be a finite set of hypotheses with prior $\pi$, $D$ a finite set of data, and $L(h)$ a probability distribution on $D$ for each hypothesis $h$. The posterior given a datum $d$ is $P(h \mid d) = \pi(h) L(h)(d) / P(d)$ when the predictive probability $P(d)$ is positive; when $P(d) = 0$ the posterior is defined to be the prior. The second case never arises for a datum with positive likelihood under a hypothesis of positive prior mass.
