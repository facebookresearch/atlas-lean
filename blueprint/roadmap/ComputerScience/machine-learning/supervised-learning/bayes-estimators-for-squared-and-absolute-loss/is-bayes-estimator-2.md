# A posterior median is a Bayes estimator for absolute loss

Let $P$ be a finite kernel from
$\mathbb{R}$ to a measurable space $\mathcal{X}$, sending a parameter $\theta$ to the measure
$P_\theta$ on $\mathcal{X}$, let $\pi$ be a finite prior measure on $\mathbb{R}$, and let
$f : \mathcal{X} \to \mathbb{R}$ be a measurable choice of posterior medians. Then the
deterministic estimator $x \mapsto f(x)$ is a Bayes estimator for the absolute loss
$\ell(\theta, y) = |\theta - y|$: its average risk
$\int \int |\theta - f(x)| \, dP_\theta(x) \, d\pi(\theta)$ equals the Bayes risk, the infimum
of the average risks of all Markov kernels from $\mathcal{X}$ to $\mathbb{R}$, where risks take
values in $[0, \infty]$.
