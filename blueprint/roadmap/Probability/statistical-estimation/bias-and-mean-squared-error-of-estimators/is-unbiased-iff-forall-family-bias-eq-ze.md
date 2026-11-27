# An estimator is unbiased exactly when its bias vanishes

Let
$(P_\theta)_{\theta \in \Theta}$ be a family of probability measures on $S$,
$\tau : \Theta \to \mathbb{R}$ a target function, and $W : S \to \mathbb{R}$ an estimator that is
$P_\theta$-integrable for every $\theta \in \Theta$. Then $W$ is unbiased for $\tau$ if and only if
its family bias $\int_S W \, dP_\theta - \tau(\theta)$ is zero for every $\theta \in \Theta$.
