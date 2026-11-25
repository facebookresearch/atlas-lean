# Weighted covariance

For a finite set $\iota$ and real vectors $v, a, b \in \mathbb{R}^\iota$, the weighted covariance of $a$ and $b$ with weights $v$ is

$$\operatorname{Cov}_v(a, b) = \frac{\sum_j v_j (a_j - \bar a_v)(b_j - \bar b_v)}{\sum_j v_j},$$

where $\bar a_v, \bar b_v$ are the [weighted means](weighted-mean.md), with the convention $x/0 = 0$. We write $\operatorname{Var}_v(a) = \operatorname{Cov}_v(a, a)$.
