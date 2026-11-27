# GRPO clipped surrogate objective

The GRPO objective is the PPO clipped surrogate with the learned advantage replaced by the group-relative advantage, plus a KL penalty to a reference policy, so that no value network is needed.

Use finite nonempty prompt and response sets $X$ and $Y$ for the population objectives on this page. Let $\rho$ be a prompt distribution, $\pi_k$ the current policy, $\pi_{\mathrm{ref}}$ a reference policy, $\epsilon \in [0,1]$ a clipping parameter, $\beta > 0$, and $A_{\pi_k}$ the population [group-relative advantage](group-relative-advantage.md) under $\pi_k$. The **on-policy GRPO clipped objective** is

$$\max_\pi\ \mathbb{E}_{x \sim \rho}\Bigl[\mathbb{E}_{y \sim \pi_k(\cdot \mid x)} \min\Bigl(\frac{\pi(y \mid x)}{\pi_k(y \mid x)} A_{\pi_k}(x,y),\ \mathrm{clip}\Bigl(\frac{\pi(y \mid x)}{\pi_k(y \mid x)}, 1-\epsilon, 1+\epsilon\Bigr) A_{\pi_k}(x,y)\Bigr) - \beta\, \mathrm{KL}\bigl(\pi(\cdot \mid x) \,\|\, \pi_{\mathrm{ref}}(\cdot \mid x)\bigr)\Bigr].$$

In the **off-policy** form the samples and the advantage statistics come from a sampling policy $\alpha$, such as an earlier iterate $\pi_{k-v}$: with $f_\epsilon(u, u', a) = \min\bigl(u a,\ \mathrm{clip}(u, \max(u' - \epsilon, 0), u' + \epsilon)\, a\bigr)$ and

$$L^{c}_\alpha(\pi(\cdot \mid x)) = \mathbb{E}_{y \sim \alpha(\cdot \mid x)}\, f_\epsilon\Bigl(\frac{\pi(y \mid x)}{\alpha(y \mid x)}, \frac{\pi_k(y \mid x)}{\alpha(y \mid x)}, A_\alpha(x,y)\Bigr),$$

the objective is $\mathbb{E}_{x \sim \rho}\bigl[L^{c}_\alpha(\pi(\cdot \mid x)) - \beta\, \mathrm{KL}(\pi(\cdot \mid x) \,\|\, \pi_{\mathrm{ref}}(\cdot \mid x))\bigr]$; $\alpha = \pi_k$ gives the on-policy form. In both forms the inner expectation sums only over responses with positive sampling probability, so its ratios are defined almost surely; the outer expectation sums only over prompts with $\rho(x)>0$. The finite-space KL divergence takes values in $[0,\infty]$ and is $+\infty$ exactly when absolute continuity fails. The overall objective is therefore $-\infty$ if absolute continuity of $\pi(\cdot\mid x)$ with respect to $\pi_{\mathrm{ref}}(\cdot\mid x)$ fails for some prompt with $\rho(x)>0$, and is finite otherwise. A prompt of probability zero contributes nothing. This is a finite-space specialization of the source's population objectives, not a claim that point probabilities give density ratios for continuous responses.

In the **token-level sample form** used to train language models, for each question $q$ a group of $G \ge 2$ nonempty outputs $o_1, \dots, o_G$ (each $|o_i| \ge 1$ tokens) is drawn from $\pi_{\theta_{\mathrm{old}}}(\cdot \mid q)$ and $\theta$ maximizes the expectation of

$$\frac{1}{G} \sum_{i=1}^{G} \frac{1}{|o_i|} \sum_{t=1}^{|o_i|} \Bigl\{\min\bigl(\rho_{i,t}(\theta) \hat A_{i,t},\ \mathrm{clip}(\rho_{i,t}(\theta), 1-\epsilon, 1+\epsilon) \hat A_{i,t}\bigr) - \beta\, \hat D_{i,t}(\theta)\Bigr\},$$

where $\rho_{i,t}(\theta) = \pi_\theta(o_{i,t} \mid q, o_{i,<t})/\pi_{\theta_{\mathrm{old}}}(o_{i,t} \mid q, o_{i,<t})$, $\hat A_{i,t} = \hat A_i$ is the [group estimate](group-relative-advantage.md) for response $o_i$ with the same $\varepsilon > 0$ and the divisor $G$ in $s^2$, assigned to every token of $o_i$, and $\hat D_{i,t} = u - \log u - 1$, with $\log$ the natural logarithm, with $u = \pi_{\mathrm{ref}}(o_{i,t} \mid q, o_{i,<t})/\pi_\theta(o_{i,t} \mid q, o_{i,<t})$ is a per-token estimate of the KL penalty; it requires $\pi_\theta$ and $\pi_{\mathrm{ref}}$ to give positive probability to the sampled tokens (as softmax policies do), while $\pi_{\theta_{\mathrm{old}}}(o_{i,t} \mid q, o_{i,<t}) > 0$ holds because the tokens were drawn from it.

## Depends on

- [Group-relative advantage](group-relative-advantage.md)
- [PPO clipped surrogate objective](../trust-region-and-clipped-surrogates/ppo-clipped-surrogate-objective.md)
- [Kullback–Leibler divergence on a finite space](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

None.

## Expansion

Iterative GRPO takes several gradient steps on each sampled batch and periodically resets $\pi_{\mathrm{ref}}$ to the current policy. After the first step on a batch the advantage statistics no longer describe the policy being optimized, which is one reason Mroueh et al. treat GRPO with sample reuse as off-policy. The per-sequence average $1/|o_i|$ is one of several weightings in use: Fontana et al. tabulate variants that average over all tokens of the group, use the constant weight $1/G$, or mask some responses, and show that sequence-dependent weights bias the gradient on shared prefixes ([shared-prefix gradients under group weights](shared-prefix-gradients-under-group-weights.md)). With length-normalized weights at $\theta = \theta_{\mathrm{old}}$, the reward-driven part of the surrogate's value is a multiple of $\sum_i \hat A_i = 0$, so the value of the surrogate is not a measure of reward improvement.

Maximizing this clipped objective is motivated by the [GRPO policy improvement lower bound](grpo-policy-improvement-lower-bound.md), which concerns the unclipped importance-weighted advantage under a total variation constraint, but no improvement guarantee is proved for the clipped objective itself.

## Sources

- Z. Shao, P. Wang, Q. Zhu, R. Xu, J. Song, X. Bi, H. Zhang, M. Zhang, Y. K. Li, Y. Wu and D. Guo, *DeepSeekMath: Pushing the Limits of Mathematical Reasoning in Open Language Models*, preprint, arXiv:2402.03300v3, Section 4.1.1, equations (3) and (4), and Algorithm 1.
- Y. Mroueh, N. Dupuis, B. Belgodere, A. Nitsure, M. Rigotti, K. Greenewald, J. Navratil, J. Ross and J. Rios, *Revisiting Group Relative Policy Optimization: Insights into On-Policy and Off-Policy Training*, International Conference on Learning Representations (ICLR 2026), Section 2, Section 3.2 (the function $f_\epsilon$, the clipped off-policy objective and equation (6)) and Algorithm 1. [PDF](https://proceedings.iclr.cc/paper_files/paper/2026/file/b4008025c2182bfe16fcc8566ee14d64-Paper-Conference.pdf)
- A. Fontana, M. Simoni, G. Rossolini, P. Mori and A. Saracino, *On the Hidden Objective Biases of Group-based Reinforcement Learning*, Proceedings of the 64th Annual Meeting of the Association for Computational Linguistics (Volume 2: Short Papers), ACL 2026, pages 109–121, equation (1), Table 1, and Appendix A.1 (Proposition 4, Case 1). [publisher page](https://aclanthology.org/2026.acl-short.11/)
