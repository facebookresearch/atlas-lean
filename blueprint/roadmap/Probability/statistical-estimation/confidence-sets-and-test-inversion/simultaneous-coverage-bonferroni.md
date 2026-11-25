# Bonferroni simultaneous coverage

Let $(P_\theta)_{\theta \in \Theta}$ be probability measures on a measurable space $\mathcal X$, and for $j = 1, \dots, m$ let $\tau_j$ be an estimand with values in $\mathcal T_j$, $C_j$ a map from observations to subsets of $\mathcal T_j$ with $\{x : \tau_j(\theta) \in C_j(x)\}$ measurable, and $\alpha_j \in \mathbb{R}$ with $P_\theta(\tau_j(\theta) \in C_j(x)) \ge 1 - \alpha_j$ for every $\theta$. Then for every $\theta$

$$P_\theta\big(\tau_j(\theta) \in C_j(x) \text{ for all } j\big) \ge 1 - \sum_{j=1}^m \alpha_j.$$
