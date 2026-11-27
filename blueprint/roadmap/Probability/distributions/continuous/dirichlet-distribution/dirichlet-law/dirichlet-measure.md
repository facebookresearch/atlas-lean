# Dirichlet distribution

Let $\alpha = (\alpha_0, \dots, \alpha_n) \in \mathbb{R}^{n+1}$, let
$D_\alpha$ be the unnormalized Dirichlet density on $\mathbb{R}^n$ with parameters $\alpha$, and let
$B(\alpha) = \prod_{i=0}^{n} \Gamma(\alpha_i) / \Gamma(\sum_{i=0}^{n} \alpha_i)$ be the
multivariate Beta function. The Dirichlet distribution $\mathrm{Dir}(\alpha)$ is the measure on
$\mathbb{R}^{n+1}$ obtained by pushing forward the measure on $\mathbb{R}^n$ with density
$D_\alpha(x) / B(\alpha)$ with respect to Lebesgue measure along the map
$x \mapsto (x_0, \dots, x_{n-1}, 1 - \sum_{i=0}^{n-1} x_i)$.

The quotient is taken in $[0, \infty]$, with a nonpositive $B(\alpha)$ read as $0$; this matters
only when some $\alpha_i \le 0$. For positive parameters $\mathrm{Dir}(\alpha)$ is a probability
measure concentrated on vectors with positive entries summing to $1$.
