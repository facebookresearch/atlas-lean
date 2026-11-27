# Reward modeling and DPO as Ψ-preference optimization

With the logit transform $\Psi(q) = \log(q/(1-q))$ and Bradley–Terry preferences, Ψ-preference optimization and KL-regularized maximization of the Bradley–Terry reward have the same optimal policy, and that policy minimizes the population DPO loss.

Let $X$ and $Y$ be finite, $\rho$ a distribution on $X$, $\mu$ a behavior policy, $\tau > 0$ and $\pi_{\mathrm{ref}}$ a reference policy. Suppose the preferences follow the [Bradley–Terry model](bradley-terry-and-plackett-luce-models.md) with a reward $r$, that is $p^*(y \succ y' \mid x) = \sigma(r(x,y) - r(x,y'))$ for all $x, y, y'$; these probabilities lie in $(0,1)$, where $\Psi(q) = \log(q/(1-q))$ is applied. Then for every $x$ and $y$

$$\mathbb{E}_{y' \sim \mu(\cdot \mid x)}\Bigl[\Psi\bigl(p^*(y \succ y' \mid x)\bigr)\Bigr] = r(x,y) - \mathbb{E}_{y' \sim \mu(\cdot \mid x)}\, r(x,y'),$$

a reward equivalent to $r$, so the [ΨPO objective](psi-preference-optimization.md) with this $\Psi$ and [KL-regularized reward maximization](kl-regularized-reward-maximization.md) of $r$ with $\beta = \tau$ have the same optimal policy, the [KL-regularized optimal policy](optimal-policy-of-kl-regularized-rewards.md) $\pi_r$. If moreover $\pi_{\mathrm{ref}}(y \mid x) > 0$ for all $x, y$, then $\pi_r$ is a minimizer of the population [DPO loss](direct-preference-optimization-loss.md) over policies with full support.

## Depends on

- [Bradley–Terry and Plackett–Luce preference models](bradley-terry-and-plackett-luce-models.md)
- [Ψ-preference optimization](psi-preference-optimization.md)
- [KL-regularized reward maximization](kl-regularized-reward-maximization.md)
- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)
- [Direct preference optimization loss](direct-preference-optimization-loss.md)

## Proof depends on

- [Equivalent rewards induce the same KL-regularized optimal policy](equivalent-rewards-give-equal-optimal-policies.md)
- [DPO and KL-regularized reward maximization have the same optimal policies](dpo-and-rlhf-have-equal-optimal-policies.md)
- [Gibbs' inequality](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)

## Expansion

Since $\Psi(\sigma(t)) = t$, the expectation equals $\mathbb{E}_{y'}[r(x,y) - r(x,y')]$, which differs from $r(x,y)$ by a function of $x$ alone, and equivalent rewards have the same KL-regularized optimal policy. For the DPO part, the Bradley–Terry reward $r$ minimizes the population Bradley–Terry loss when $p^*$ follows the Bradley–Terry model with reward $r$: pairing each ordered pair $(y, y')$ with $(y', y)$, which has the same weight $\mu(y \mid x)\mu(y' \mid x)$, and using $p^*(y' \succ y \mid x) = 1 - p^*(y \succ y' \mid x)$, the loss is an average of binary cross-entropies between $p^*(y \succ y' \mid x)$ and $\sigma(\hat r(x,y) - \hat r(x,y'))$, each smallest when the two agree, as they do for $\hat r = r$. The theorem on DPO and KL-regularized maximization then shows that $\pi_r$ minimizes the population DPO loss.

The source states that the three optimal policies are identical. As the DPO statement above is phrased, $\pi_r$ is a minimizer; the population DPO loss only involves responses drawn from $\mu$, so when $\mu(\cdot \mid x)$ does not charge every response its minimizers need not be unique (with three responses and $\mu$ uniform on two of them, the loss depends only on the ratio of the first two probabilities). The optimal policy of the first two problems is $\pi^*(y \mid x) \propto \pi_{\mathrm{ref}}(y \mid x) \exp\bigl(\tau^{-1} \mathbb{E}_{y'} \Psi(p^*(y \succ y' \mid x))\bigr)$, equation (7) of the source.

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Proposition 1 and its proof (Section 4.1), equation (7), and Proposition 4 (Appendix B) for the DPO part. [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Appendix A.6 of the supplementary material (the hypothesis $\pi_{\mathrm{ref}}(y \mid x) > 0$). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
