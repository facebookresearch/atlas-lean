# Environmental noise cannot raise the expected steady-state harvest above the deterministic MSY

**Model.** A population with pre-harvest size $Y_t$ is harvested by a stationary policy $h$, leaving escapement $u(y)=y-h(y)$, and then reproduces in a random environment $\xi_{t+1}$ (i.i.d.):

$$Y_{t+1}=u(Y_t)\,f\big(u(Y_t),\xi_{t+1}\big).$$

Let $\bar f(x)=\mathbb{E}f(x,\xi_1)$, $\bar F(x)=x\bar f(x)$ and $\bar G(x)=\bar F(x)-x$. The averaged deterministic model $x_{t+1}=x_t\bar f(x_t)$ has equilibrium yield $\bar G(u(y))$, and its **deterministic maximum sustainable yield** is $M_{\det}=\max_x\bar G(x)=\bar G(x_1)$. Persistence under harvesting requires $\mathbb{E}\ln\big(u'(0)f(0,\xi_1)\big)>0$. When $Y_t$ converges to a stationary law $\pi_u$ with $Y_\infty\sim\pi_u$, the long-run average and expected yields both converge to the **expected steady-state yield** $\mathbb{E}h(Y_\infty)$.

**Theorem.**
1. For every stationary policy, $\mathbb{E}h(Y_\infty)\le M_{\det}$. Equality holds only if (i) the unharvested dynamics can reach levels $\ge x_1$, (ii) the policy is bang-bang with threshold $x_1$, $h^*(y)=(y-x_1)^+$, and (iii) $x_1$ is self-sustaining (once reached, noise never pushes the population below it).
2. *(Constant effort.)* If $\bar F$ is strictly concave and the dynamics is genuinely random, every constant-effort policy $h_\theta(y)=\theta y$ has expected steady-state yield strictly below its deterministic yield.
3. *(Bang-bang thresholds.)* For $h_w(y)=(y-w)^+$ with $w$ self-sustaining, $\mathbb{E}h_w(Y_\infty)=\bar G(w)$, with variance $w^2\,\mathbb{E}\big[f(w,\xi_1)^2-\bar f(w)^2\big]$ (positive unless $f(w,\xi_1)$ is almost surely constant). If $w$ is not self-sustaining while the levels near the maximizer of a unimodal $\bar G$ are, the stochastic expected yield of $h_w$ can strictly exceed its deterministic nominal yield $\bar G(w)$.

## Expansion

At stationarity $Y_\infty$ and $u(Y_\infty)f(u(Y_\infty),\xi_1)$ have the same law, with $\xi_1$ independent of $Y_\infty$, so

$$\mathbb{E}h(Y_\infty)=\mathbb{E}Y_\infty-\mathbb{E}u(Y_\infty)=\mathbb{E}\,\bar G\big(u(Y_\infty)\big)\le\max\bar G=M_{\det},$$

with equality only if the escapement $u(Y_\infty)$ sits at $x_1$ almost surely, which forces the bang-bang policy and a self-sustaining threshold. For constant effort, $\mathbb{E}Y_\infty=\frac{1}{1-\theta}\mathbb{E}\bar F\big((1-\theta)Y_\infty\big)$, and Jensen's inequality for strictly concave $\bar F$ gives the strict loss. Environmental fluctuations are therefore generically detrimental to yield, and even when the mean is preserved the yield becomes variable.

## Sources

- Alexandru Hening, "Coexistence, extinction, and optimal harvesting in discrete-time stochastic population models", arXiv:1911.08398 (2019), Section 3, Theorems 3.1–3.2 and the two propositions on bang-bang threshold harvesting, <https://doi.org/10.48550/arXiv.1911.08398>.
