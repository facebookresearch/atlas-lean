# Group-relative REINFORCE as a gradient step on a consistency loss

For any group of responses to one prompt, however the responses were sampled, the group-relative REINFORCE direction (each reward minus the group mean, times the score function) is a positive multiple of minus the gradient of a pairwise consistency loss at the current policy.

Let $x$ be a prompt, $y_1, \dots, y_K$ ($K \ge 2$) responses with rewards $r_i = r(x, y_i)$ and mean $\bar r = \frac1K \sum_j r_j$, let $\pi_\theta$ be a policy parameterized by $\theta$ in an open subset of $\mathbb{R}^d$, with $\pi_{\theta_t}(y_i \mid x) > 0$ and $\theta \mapsto \log \pi_\theta(y_i \mid x)$ differentiable at the current parameter $\theta_t$, and let $\tau > 0$. The **group-relative REINFORCE** direction is

$$g = \frac{1}{K} \sum_{i=1}^{K} (r_i - \bar r)\, \nabla_\theta \log \pi_\theta(y_i \mid x)\big|_{\theta = \theta_t},$$

whose baseline is the group mean, including the response's own reward. With $a_i(\theta) = r_i - \tau\bigl(\log \pi_\theta(y_i \mid x) - \log \pi_{\theta_t}(y_i \mid x)\bigr)$ define the pairwise consistency loss

$$\hat L(\theta) = \frac{1}{K^2} \sum_{1 \le i < j \le K} \frac{(a_i(\theta) - a_j(\theta))^2}{(1+\tau)^2}.$$

Then

$$-\nabla_\theta \hat L(\theta_t) = \frac{2\tau}{(1+\tau)^2}\, g.$$

No assumption is made on the distribution of $y_1, \dots, y_K$.

## Depends on

None.

## Proof depends on

None.

## Expansion

At $\theta = \theta_t$ the log-ratio terms vanish, so $a_i - a_j = r_i - r_j$ and $\nabla_\theta (a_i - a_j)^2 = -2\tau (r_i - r_j)(\nabla_\theta \log \pi_\theta(y_i \mid x) - \nabla_\theta \log \pi_\theta(y_j \mid x))$. Summing over pairs, $\sum_{i<j} (r_i - r_j)(v_i - v_j) = \sum_{i,j} (r_i - r_j) v_i = K \sum_i (r_i - \bar r) v_i$ for any vectors $v_i$, and dividing by $K^2(1+\tau)^2$ gives the identity.

The loss enforces the consistency condition $r_i - \tau \log(\pi(y_i \mid x)/\pi_{\theta_t}(y_i \mid x)) = r_j - \tau \log(\pi(y_j \mid x)/\pi_{\theta_t}(y_j \mid x))$, which characterizes, on its support, the maximizer $\pi \propto \pi_{\theta_t} e^{r/\tau}$ of the KL-regularized surrogate $\mathbb{E}_{y \sim \pi} r(x,y) - \tau\, \mathrm{KL}(\pi \,\|\, \pi_{\theta_t})$ ([optimal policy of KL-regularized reward maximization](../kl-regularized-preference-learning/optimal-policy-of-kl-regularized-rewards.md) with $\pi_{\mathrm{ref}} = \pi_{\theta_t}$). Group-relative REINFORCE thus takes one gradient step on a surrogate loss for a KL-regularized step from the current policy, a reading that, unlike the on-policy view through the [policy gradient theorem](../../policy-gradient-theorem.md), does not require the responses to be drawn from $\pi_{\theta_t}$. Yao et al. stress that this does not imply convergence to an optimal policy from arbitrary training data. The identity concerns the centred, unnormalized direction; the GRPO advantage further divides by the group standard deviation.

## Sources

- C. Yao, Y. Chen, Y. Sun, Y. Chen, W. Zhang, X. Pan, Y. Li and B. Ding, *Group-Relative REINFORCE Is Secretly an Off-Policy Algorithm: Demystifying Some Myths About GRPO and Its Friends*, International Conference on Learning Representations (ICLR 2026), Section 1, equation (1a), and Section 2.2, equations (3) to (7). [publisher page](https://proceedings.iclr.cc/paper_files/paper/2026/hash/6cad062f78120689e8a678b8af9c6d92-Abstract-Conference.html)
