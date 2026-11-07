# Mean squared error is frequentist risk under squared-error loss

Let
$(P_\theta)_{\theta \in \Theta}$ be a family of probability measures on $S$,
$W : S \to \mathbb{R}$ an estimator and $\tau : \Theta \to \mathbb{R}$ a target function such that
$x \mapsto (W(x) - \tau(\theta))^2$ is $P_\theta$-integrable for every $\theta \in \Theta$. Then for
every $\theta$, the frequentist risk at $\theta$ of $W$, as a decision rule with actions in
$\mathbb{R}$, under the squared-error loss $\ell(\theta, a) = (a - \tau(\theta))^2$ equals the
family mean squared error of $W$ for $\tau$ at $\theta$.

## Sources

- blueprint `af_36871388da7326a07a5e4f71`.
