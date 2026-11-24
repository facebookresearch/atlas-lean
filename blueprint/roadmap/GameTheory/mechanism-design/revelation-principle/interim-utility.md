# Interim expected utility

Let $I$ be a finite set of agents with finite type sets $\Theta_i$, and $O$ a set of outcomes. For a real
function $p$ on the finite set of type profiles $\prod_j \Theta_j$ (a prior), utilities
$u_i(\theta, o) \in \mathbb{R}$ that may depend on the whole type profile, an agent $i$, a type
$\theta_i^0 \in \Theta_i$ and an outcome function $h : \prod_j \Theta_j \to O$, the interim expected utility
of agent $i$ of type $\theta_i^0$ is

$$U_i(\theta_i^0, h) = \sum_{\theta :\ \theta_i = \theta_i^0} p(\theta)\, u_i(\theta, h(\theta)).$$

For a probability distribution $p$ this is Myerson's $Z_i$ (1979, equation (5)) multiplied by the marginal
probability of $\theta_i^0$, so the incentive constraints written with it are those of Myerson (1979, (6))
whenever that marginal is positive, and are vacuous when it is zero.

## Sources

- R. B. Myerson, "Incentive compatibility and the bargaining problem", *Econometrica* 47(1) (1979), 61–73, §2, (4) and (5).
