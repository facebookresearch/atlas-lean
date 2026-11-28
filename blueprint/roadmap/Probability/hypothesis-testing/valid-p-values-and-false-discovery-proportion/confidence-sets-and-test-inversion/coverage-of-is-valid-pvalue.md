# Inverting valid p-values gives a confidence set

Let $(P_\theta)_{\theta \in \Theta}$ be probability measures on a measurable space $\mathcal X$ of observations and $\tau : \Theta \to \mathcal T$ an estimand. For each $t \in \mathcal T$ let $p_t : \mathcal X \to \mathbb{R}$ be measurable, and suppose $p_{\tau(\theta)}$ is a valid p-value under $P_\theta$ for every $\theta$ ($P_\theta(p_{\tau(\theta)} \le s) \le s$ for $s \in [0,1]$). Then for every $\alpha \in [0,1]$ and every $\theta$ the set $C(x) = \{t : p_t(x) > \alpha\}$ satisfies

$$P_\theta\big(\tau(\theta) \in C(x)\big) \ge 1 - \alpha.$$
