# Direct preference optimization loss

Direct preference optimization (DPO) fits a policy to a fixed dataset of pairwise comparisons by maximum likelihood in the Bradley–Terry model whose reward is the implicit reward $\beta \log(\pi_\theta/\pi_{\mathrm{ref}})$. It needs no separate reward model, no sampling from the policy during training and no reinforcement-learning loop.

Let $\mathcal{D} = \{(x^{(i)}, y_w^{(i)}, y_l^{(i)})\}_{i=1}^{N}$, with $N \ge 1$, be a finite dataset of comparisons in which $y_w^{(i)}$ was preferred to $y_l^{(i)}$, let $\pi_{\mathrm{ref}}$ be a reference policy, $\beta > 0$, and $\pi_\theta$ a parameterized policy, with $\pi_\theta(y \mid x) > 0$ and $\pi_{\mathrm{ref}}(y \mid x) > 0$ for the pairs in $\mathcal{D}$. The implicit reward of $\pi_\theta$ is $\hat r_\theta(x,y) = \beta \log\bigl(\pi_\theta(y \mid x)/\pi_{\mathrm{ref}}(y \mid x)\bigr)$, and the **DPO loss** is

$$\mathcal{L}_{\mathrm{DPO}}(\pi_\theta; \pi_{\mathrm{ref}}) = -\mathbb{E}_{(x, y_w, y_l) \sim \mathcal{D}} \log \sigma\Bigl(\beta \log \frac{\pi_\theta(y_w \mid x)}{\pi_{\mathrm{ref}}(y_w \mid x)} - \beta \log \frac{\pi_\theta(y_l \mid x)}{\pi_{\mathrm{ref}}(y_l \mid x)}\Bigr),$$

the average over $\mathcal{D}$; it is the [Bradley–Terry negative log-likelihood](bradley-terry-and-plackett-luce-models.md) $\mathcal{L}_R(\hat r_\theta, \mathcal{D})$ of the implicit reward. For finite nonempty prompt and response sets $X$ and $Y$, a prompt distribution $\rho$, a behavior policy $\mu$, and preference probabilities $p^*(y \succ y' \mid x) \in [0,1]$, define the population DPO loss for full-support policies $\pi$ and $\pi_{\mathrm{ref}}$, satisfying $\pi(y \mid x) > 0$ and $\pi_{\mathrm{ref}}(y \mid x) > 0$ for every $x \in X$ and $y \in Y$, by

$$\mathcal{L}_{\mathrm{DPO}}(\pi) = -\mathbb{E}_{x \sim \rho,\ y, y' \sim \mu(\cdot \mid x)}\Bigl[p^*(y \succ y' \mid x) \log \sigma\Bigl(\beta \log \frac{\pi(y \mid x)}{\pi_{\mathrm{ref}}(y \mid x)} - \beta \log \frac{\pi(y' \mid x)}{\pi_{\mathrm{ref}}(y' \mid x)}\Bigr)\Bigr],$$

that is, the population Bradley–Terry loss of $\hat r = \beta \log(\pi/\pi_{\mathrm{ref}})$. For datasets of rankings, the Plackett–Luce version replaces $\log \sigma(\cdot)$ by the logarithm of the Plackett–Luce probability of the observed ranking computed with the implicit rewards.

## Depends on

- [Bradley–Terry and Plackett–Luce preference models](bradley-terry-and-plackett-luce-models.md)

## Proof depends on

None.

## Expansion

The loss comes from [expressing Bradley–Terry preferences through the KL-regularized optimal policy](preferences-in-terms-of-the-optimal-policy.md) and replacing that policy by $\pi_\theta$: one fits an implicit reward whose KL-regularized optimal policy is $\pi_\theta$ itself ([reward reparameterization](reward-reparameterization-by-optimal-policy.md)), and the optimal policies of DPO and of KL-regularized maximization of the fitted Bradley–Terry reward coincide ([theorem](dpo-and-rlhf-have-equal-optimal-policies.md)).

DPO is an offline objective, not an online reinforcement-learning algorithm. In the original pipeline the comparisons are collected once, from responses sampled from the supervised fine-tuned model (used as $\pi_{\mathrm{ref}}$) and labeled by people, and $\mathcal{L}_{\mathrm{DPO}}$ is then minimized on that fixed dataset; minimizing it does not draw responses from $\pi_\theta$. The gradient is

$$\nabla_\theta \mathcal{L}_{\mathrm{DPO}} = -\beta\, \mathbb{E}_{(x, y_w, y_l) \sim \mathcal{D}}\Bigl[\sigma\bigl(\hat r_\theta(x, y_l) - \hat r_\theta(x, y_w)\bigr)\bigl(\nabla_\theta \log \pi_\theta(y_w \mid x) - \nabla_\theta \log \pi_\theta(y_l \mid x)\bigr)\Bigr],$$

which raises the likelihood of preferred responses and lowers that of dispreferred ones, weighting each comparison by how strongly the implicit reward misorders it. With deterministic or nearly deterministic preferences the implicit reward gaps are pushed to infinity, a failure mode analyzed by Gheshlaghi Azar et al. and addressed by the [IPO loss](identity-preference-optimization-loss.md).

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Section 4, equation (7), the gradient display and the DPO outline, and Appendices A.3 and A.4 of the supplementary material (Plackett–Luce loss and gradient derivation). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Section 3.2, equations (4) and (5) (empirical and population forms), and Section 4.2. [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
