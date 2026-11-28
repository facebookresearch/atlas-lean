# Reward reparameterization through the optimal policy

When the reference policy charges every response, each reward is equivalent to exactly one reward of the form $\beta \log(\pi(y \mid x)/\pi_{\mathrm{ref}}(y \mid x))$, namely the log-ratio of its own KL-regularized optimal policy, so this parameterization of rewards by policies loses no reward class.

Let $X$ and $Y$ be finite, $\beta > 0$, and let $\pi_{\mathrm{ref}}$ satisfy $\pi_{\mathrm{ref}}(y \mid x) > 0$ for all $x$ and $y$. For a reward $r$ let $Z$ and $\pi_r$ be the partition function and [optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md). Then

$$r(x,y) = \beta \log \frac{\pi_r(y \mid x)}{\pi_{\mathrm{ref}}(y \mid x)} + \beta \log Z(x) \qquad \text{for all } x, y,$$

so the reward $r(x,y) - \beta \log Z(x) = \beta \log\bigl(\pi_r(y \mid x)/\pi_{\mathrm{ref}}(y \mid x)\bigr)$ is [equivalent](equivalent-reward-functions.md) to $r$. Every equivalence class of rewards contains exactly one reward of the form

$$r_\pi(x,y) = \beta \log \frac{\pi(y \mid x)}{\pi_{\mathrm{ref}}(y \mid x)}$$

with $\pi$ a policy such that $\pi(y \mid x) > 0$ for all $x, y$; in the class of $r$ it is $r_{\pi_r}$, the same for every member of the class. Conversely, the KL-regularized optimal policy of $r_\pi$ is $\pi$ itself, since its partition function is $1$.

## Depends on

- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)
- [Equivalent reward functions](equivalent-reward-functions.md)

## Proof depends on

- [Equivalent rewards induce the same KL-regularized optimal policy](equivalent-rewards-give-equal-optimal-policies.md)

## Expansion

The first identity is the logarithm of $\pi_r(y \mid x) Z(x) = \pi_{\mathrm{ref}}(y \mid x) e^{r(x,y)/\beta}$, and $\beta \log Z(x)$ depends on $x$ only. Equivalent rewards have the same optimal policy, so the normalizing map $r \mapsto r - \beta \log Z_r$ sends a whole class to the single reward $r_{\pi_r}$. For uniqueness, suppose $r_{\pi'} = r_\pi + f(x)$ for full-support policies $\pi, \pi'$. Then $\pi(y \mid x) e^{f(x)/\beta} = \pi'(y \mid x)$ for all $y$; summing over $y$ gives $e^{f(x)/\beta} = 1$, so $f = 0$ and the two rewards coincide. Finally $\sum_y \pi_{\mathrm{ref}}(y \mid x) e^{r_\pi(x,y)/\beta} = \sum_y \pi(y \mid x) = 1$, which is how the reparameterization selects one member of each class.

This is the sense in which a language model is secretly a reward model: fitting a Bradley–Terry model over rewards $r_\pi$ ranges over every reward class, while the optimal policy of the fitted reward is the fitted $\pi$, available without a reinforcement-learning loop; see the [DPO loss](direct-preference-optimization-loss.md). The positivity of $\pi$ is needed for $r_\pi$ to be a real-valued reward.

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, equation (5) (Section 4), Theorem 1 and equation (9) (Section 5.1), and Appendix A.6 of the supplementary material (Theorem 1 restated with the hypotheses $\pi_{\mathrm{ref}}(y \mid x) > 0$ and $\beta > 0$, and Proposition 1, uniqueness). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
