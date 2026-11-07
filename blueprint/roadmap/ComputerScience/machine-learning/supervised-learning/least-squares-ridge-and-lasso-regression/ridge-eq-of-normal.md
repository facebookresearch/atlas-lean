# Expansion of the ridge objective around a solution of its normal equations

Let $X$ be a
real matrix with $m$ rows and columns indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$
and $\lambda \in \mathbb{R}$, and write $\|\cdot\|$ for the Euclidean norm and
$R(\theta) = \|y - X\theta\|^2 + \lambda \|\theta\|^2$ for the ridge objective. If
$\theta_0 \in \mathbb{R}^\iota$ satisfies $(X^\top X + \lambda I)\theta_0 = X^\top y$, then for
every $\theta \in \mathbb{R}^\iota$,
$R(\theta) = R(\theta_0) + \|X(\theta - \theta_0)\|^2 + \lambda \|\theta - \theta_0\|^2$.
