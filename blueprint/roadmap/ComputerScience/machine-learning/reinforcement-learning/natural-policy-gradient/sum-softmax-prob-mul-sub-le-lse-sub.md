# Convexity of the log-partition function

For logits $\theta, \theta'$ and a state $s$,

$$\sum_b \pi_\theta(b \mid s)\bigl(\theta'(s,b) - \theta(s,b)\bigr) \le \operatorname{lse}_{\theta'}(s) - \operatorname{lse}_\theta(s),$$

by Jensen's inequality for $\exp$: the gradient of $\operatorname{lse}$ at $\theta$ is $\pi_\theta$.
