# PPO clipped surrogate objective

The clipped surrogate of proximal policy optimization (PPO) multiplies each advantage estimate by the probability ratio between the new and old policy, clips the ratio to $[1-\epsilon, 1+\epsilon]$ in a second copy, and keeps the smaller of the two terms.

Let a batch of timesteps $t$ be collected by running a policy $\pi_{\theta_{\mathrm{old}}}$, with states $s_t$, actions $a_t$ and advantage estimates $\hat A_t$, and let $\hat{\mathbb{E}}_t$ denote the average over the batch. For a parameter $\theta$ the probability ratio is $r_t(\theta) = \pi_\theta(a_t \mid s_t)/\pi_{\theta_{\mathrm{old}}}(a_t \mid s_t)$, so $r_t(\theta_{\mathrm{old}}) = 1$. The conservative surrogate is $L^{\mathrm{CPI}}(\theta) = \hat{\mathbb{E}}_t[r_t(\theta) \hat A_t]$, and for a clipping parameter $\epsilon \in (0,1)$ the **clipped surrogate objective** is

$$L^{\mathrm{CLIP}}(\theta) = \hat{\mathbb{E}}_t\Bigl[\min\bigl(r_t(\theta)\, \hat A_t,\ \mathrm{clip}(r_t(\theta), 1-\epsilon, 1+\epsilon)\, \hat A_t\bigr)\Bigr],$$

where $\mathrm{clip}(u, a, b) = \min(\max(u, a), b)$. Each term equals $(1-\epsilon)\hat A_t$ when $r_t(\theta) \le 1-\epsilon$ and $\hat A_t < 0$, equals $(1+\epsilon)\hat A_t$ when $r_t(\theta) \ge 1+\epsilon$ and $\hat A_t > 0$, and equals $r_t(\theta) \hat A_t$ otherwise; in the first two cases its gradient in $\theta$ vanishes. PPO maximizes $L^{\mathrm{CLIP}}$ by several epochs of minibatch stochastic gradient ascent on each batch.

## Depends on

- [Advantage function](../../performance-difference-lemma/advantage.md)

## Proof depends on

None.

## Expansion

Termwise $\min(r_t \hat A_t, \mathrm{clip}(r_t, 1-\epsilon, 1+\epsilon)\hat A_t) \le r_t \hat A_t$, so $L^{\mathrm{CLIP}} \le L^{\mathrm{CPI}}$, with equality at $\theta_{\mathrm{old}}$ and the same gradient there; this is the sense of PPO's description of the objective as a pessimistic (lower) bound, which concerns the surrogate $L^{\mathrm{CPI}}$, not the return of the updated policy. $L^{\mathrm{CPI}}$ is an importance-sampled estimate of the [local surrogate](local-surrogate-of-the-expected-return.md) up to a constant, and clipping is a heuristic replacement for the KL penalty or constraint of trust region methods: unlike the [trust-region policy improvement bound](trust-region-policy-improvement-bound.md), no monotonic improvement guarantee comes with maximizing $L^{\mathrm{CLIP}}$. Wang, He and Tan show that gradient steps on $L^{\mathrm{CLIP}}$ can push a ratio that already lies outside the clipping range further out (their Theorem 2), and that keeping the sampled ratio inside the range does not bound the KL divergence ([ratio clipping does not bound the KL divergence](ratio-clipping-does-not-bound-kl-divergence.md)).

For language models, the same objective is applied per token with ratios $\pi_\theta(o_t \mid q, o_{<t})/\pi_{\theta_{\mathrm{old}}}(o_t \mid q, o_{<t})$ and averaged over the tokens of each output; [GRPO](../group-relative-policy-optimization/grpo-clipped-surrogate-objective.md) replaces the learned advantage by a group-relative one.

## Sources

- J. Schulman, F. Wolski, P. Dhariwal, A. Radford and O. Klimov, *Proximal Policy Optimization Algorithms*, preprint, arXiv:1707.06347v2, Section 3, equations (6) and (7), and Section 5.
- Y. Wang, H. He and X. Tan, *Truly Proximal Policy Optimization*, Proceedings of the 35th Conference on Uncertainty in Artificial Intelligence (UAI 2019), PMLR 115, Section 4, equations (4) and (7a) to (7b), and Theorem 2. [publisher page](https://proceedings.mlr.press/v115/wang20b.html)
- Y. Mroueh, N. Dupuis, B. Belgodere, A. Nitsure, M. Rigotti, K. Greenewald, J. Navratil, J. Ross and J. Rios, *Revisiting Group Relative Policy Optimization: Insights into On-Policy and Off-Policy Training*, International Conference on Learning Representations (ICLR 2026), Section 2 (PPO-style clipped objective restated). [PDF](https://proceedings.iclr.cc/paper_files/paper/2026/file/b4008025c2182bfe16fcc8566ee14d64-Paper-Conference.pdf)
