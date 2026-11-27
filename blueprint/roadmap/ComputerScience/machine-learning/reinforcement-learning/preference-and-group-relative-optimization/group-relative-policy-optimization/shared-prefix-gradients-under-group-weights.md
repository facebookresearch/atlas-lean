# Shared-prefix gradients under group weights

In group-based surrogates with group-centred advantages, the gradient contribution of a prefix shared by several responses is the prefix's score function times the weighted sum of their advantages. It cancels for equal weights over the whole group but not under response-dependent weights such as length normalization.

Let $x$ be a prompt and $o_1, \dots, o_G$ responses with rewards $r_i$ and group-centred advantages $A_i = r_i - \frac1G \sum_j r_j$, so that $\sum_i A_i = 0$. Consider the surrogate

$$J(\theta) = \sum_{i=1}^{G} \sum_{t=1}^{|o_i|} \alpha_{i,t} \min\Bigl(s_{i,t}(\theta) A_i,\ \mathrm{clip}\bigl(s_{i,t}(\theta), 1 - \epsilon_{\mathrm{low}}, 1 + \epsilon_{\mathrm{up}}\bigr) A_i\Bigr) - \beta R(\theta),$$

with weights $\alpha_{i,t} \ge 0$ and ratios $s_{i,t}(\theta) = k_{i,t}\, \pi_\theta(o_{i,t} \mid x, o_{i,<t})$, where $k_{i,t} > 0$ and $\alpha_{i,t}$ do not depend on $\theta$, and $R$ is a regularizer. At a parameter $\theta$ where every term is in its unclipped branch, the gradient of the advantage part is $\sum_i A_i \sum_t \omega_{i,t} \nabla_\theta \log \pi_\theta(o_{i,t} \mid x, o_{i,<t})$ with $\omega_{i,t} = \alpha_{i,t} s_{i,t}(\theta)$. If the responses in a subset $\tilde G$ share their first $k$ tokens, $o_{i,t} = y_t$ for $i \in \tilde G$ and $t \le k$, then the contribution of these positions is

$$\sum_{t=1}^{k} \nabla_\theta \log \pi_\theta(y_t \mid x, y_{<t}) \sum_{i \in \tilde G} \omega_{i,t} A_i.$$

In particular, if $\tilde G$ is the whole group and $\omega_{i,t}$ does not depend on $i$, the contribution vanishes; if $\omega_{i,t}$ depends on $i$, for instance through a per-response token average $\alpha_{i,t} \propto 1/|o_i|$, it is a weighted sum $\sum_i \omega_{i,t} A_i$ that in general does not vanish.

## Depends on

- [Group-relative advantage](group-relative-advantage.md)
- [GRPO clipped surrogate objective](grpo-clipped-surrogate-objective.md)

## Proof depends on

None.

## Expansion

In the unclipped branch the gradient of $s_{i,t}(\theta) A_i$ is $A_i s_{i,t}(\theta) \nabla_\theta \log \pi_\theta(o_{i,t} \mid x, o_{i,<t})$ by the log-derivative identity; in the clipped branch the advantage term is locally constant and contributes no gradient. For $t \le k$ and $i \in \tilde G$ both the token and its context coincide, so the score functions are equal and factor out of the sum over $i$; $\sum_i A_i = 0$ gives the cancellation for equal weights.

With weights $1/|o_i|$, as in GRPO's per-sequence token average (at $\theta = \theta_{\mathrm{old}}$, where $s_{i,t} = 1$), shorter responses receive larger coefficients on shared prefix tokens: a short correct response pushes the common prefix up more strongly than a long one, and a short incorrect response pushes it down more strongly. Fontana et al. interpret this as a structural source of length biases, exploitable for controlling verbosity or to be mitigated. They also show that at $s_{i,t} = 1$ with length-normalized weights the reward-driven part of the surrogate's value is a multiple of $\sum_i A_i = 0$, so the value is the regularization term alone and is no measure of training progress. Their writing of GRPO uses the centred advantage $A_i$ and absorbs the standard deviation $1/\sigma(r)$ into $\alpha_{i,t}$, which leaves the group factor common to all responses.

## Sources

- A. Fontana, M. Simoni, G. Rossolini, P. Mori and A. Saracino, *On the Hidden Objective Biases of Group-based Reinforcement Learning*, Proceedings of the 64th Annual Meeting of the Association for Computational Linguistics (Volume 2: Short Papers), ACL 2026, pages 109–121, Section 3 (equations (1) to (3) and Table 1), Proposition 1 (Section 4), Appendix B.1 to B.2 (gradient derivation, equations (12) to (18), and the two cases), and Appendix A.1 (Proposition 4, Case 1). [publisher page](https://aclanthology.org/2026.acl-short.11/)
