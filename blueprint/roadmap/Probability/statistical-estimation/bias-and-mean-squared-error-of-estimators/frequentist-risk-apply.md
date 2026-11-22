# Frequentist risk as an integral

Let $S$ be a measurable space, $\delta : S \to A$ a
decision rule, $(P_\theta)_{\theta \in \Theta}$ a family of probability measures on $S$ and
$\ell : \Theta \times A \to [0, \infty)$ a loss function such that
$x \mapsto \ell(\theta, \delta(x))$ is integrable for $P_\theta$ for every $\theta \in \Theta$.
Then for every $\theta \in \Theta$ the frequentist risk of $\delta$ at $\theta$ equals
$\int_S \ell(\theta, \delta(x)) \, dP_\theta(x)$.
