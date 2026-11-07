# Candidate posterior kernel of the normal–normal model

Let $m_0 \in \mathbb{R}$ and
$v_0, v \ge 0$, let $s = \frac{v_0 v}{v_0 + v}$ be the posterior variance and, for
$x \in \mathbb{R}$, let $\mu(x) = \frac{v m_0 + v_0 x}{v_0 + v}$ be the posterior mean (with
$0 / 0 = 0$). The kernel from $\mathbb{R}$ to $\mathbb{R}$ sends $x$ to the measure with density
$\theta \mapsto \frac{1}{\sqrt{2 \pi s}} e^{-(\theta - \mu(x))^2 / (2 s)}$ with respect to Lebesgue
measure. For $v_0, v > 0$ this is the normal law $N(\mu(x), s)$. If $v_0 = 0$ or $v = 0$, then
$s = 0$, the density is taken to be $0$, and the kernel is the zero measure at every $x$.
