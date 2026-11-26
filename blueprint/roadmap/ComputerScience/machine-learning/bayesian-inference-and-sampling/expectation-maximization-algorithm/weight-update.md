# Posterior-average weight update

Let $Z$ be a finite set, let $p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values $z \in Z$, let $x_1, \dots, x_N$ be data, and write $p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior, read as $0$ when the denominator is $0$. The posterior-average weight update at the parameter $\theta$ is the function on $Z$

$$z \mapsto \frac{1}{N} \sum_{n=1}^N p_\theta(z \mid x_n),$$

read as $0$ when $N = 0$. It is defined for every joint model; nothing requires it to be positive or to sum to $1$.
