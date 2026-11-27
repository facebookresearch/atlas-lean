# DPO and KL-regularized reward maximization have the same optimal policies

If the population Bradley–Terry loss has a minimizing reward, the KL-regularized optimal policy for that reward minimizes the population DPO loss, and every DPO minimizer arises this way, whether or not the preferences follow a Bradley–Terry model.

Let $X$ and $Y$ be finite, $\rho$ a distribution on $X$, $\mu$ a policy generating the compared responses, $p^*(y \succ y' \mid x) \in [0,1]$ arbitrary preference probabilities, $\beta > 0$, and $\pi_{\mathrm{ref}}$ a reference policy with $\pi_{\mathrm{ref}}(y \mid x) > 0$ for all $x, y$. Let $\mathcal{L}_{\mathrm{BT}}$ be the population [Bradley–Terry loss](bradley-terry-and-plackett-luce-models.md) over rewards $r : X \times Y \to \mathbb{R}$, and $\mathcal{L}_{\mathrm{DPO}}$ the population [DPO loss](direct-preference-optimization-loss.md) over policies $\pi$ with $\pi(y \mid x) > 0$ for all $x, y$. For a reward $r$ let $\pi_r$ be its [KL-regularized optimal policy](optimal-policy-of-kl-regularized-rewards.md). Then $\mathcal{L}_{\mathrm{BT}}(r) = \mathcal{L}_{\mathrm{DPO}}(\pi_r)$ for every reward $r$, and:

1. if $\hat r$ minimizes $\mathcal{L}_{\mathrm{BT}}$, then $\pi_{\hat r}$ minimizes $\mathcal{L}_{\mathrm{DPO}}$;
2. if $\pi^*$ minimizes $\mathcal{L}_{\mathrm{DPO}}$, then $r^* = \beta \log(\pi^*/\pi_{\mathrm{ref}})$ minimizes $\mathcal{L}_{\mathrm{BT}}$ and $\pi^* = \pi_{r^*}$.

In particular, when $\mathcal{L}_{\mathrm{BT}}$ has a minimizer, the minimizers of $\mathcal{L}_{\mathrm{DPO}}$ are exactly the policies $\pi_{\hat r}$ with $\hat r$ a minimizer of $\mathcal{L}_{\mathrm{BT}}$. Each such $\pi_{\hat r}$ maximizes the KL-regularized objective for $\hat r$, and a policy maximizes that objective exactly when it agrees with $\pi_{\hat r}$ at every prompt with $\rho(x) > 0$. So reward modeling followed by KL-regularized maximization and minimizing the DPO loss give the same policies at every prompt with $\rho(x) > 0$; at prompts with $\rho(x) = 0$ neither problem constrains the policy beyond the full support required of DPO candidates.

## Depends on

- [Bradley–Terry and Plackett–Luce preference models](bradley-terry-and-plackett-luce-models.md)
- [Direct preference optimization loss](direct-preference-optimization-loss.md)
- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)

## Proof depends on

- [Reward reparameterization through the optimal policy](reward-reparameterization-by-optimal-policy.md)
- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)

## Expansion

By the reparameterization, $r(x,y) - r(x,y') = \beta \log(\pi_r(y \mid x)/\pi_{\mathrm{ref}}(y \mid x)) - \beta \log(\pi_r(y' \mid x)/\pi_{\mathrm{ref}}(y' \mid x))$, so the two losses agree: $\mathcal{L}_{\mathrm{BT}}(r) = \mathcal{L}_{\mathrm{DPO}}(\pi_r)$. Every full-support policy $\pi$ is $\pi_{r}$ for $r = \beta \log(\pi/\pi_{\mathrm{ref}})$, so $r \mapsto \pi_r$ maps rewards onto the domain of $\mathcal{L}_{\mathrm{DPO}}$. For 1, any admissible $\pi$ equals some $\pi_{r'}$ and $\mathcal{L}_{\mathrm{DPO}}(\pi) = \mathcal{L}_{\mathrm{BT}}(r') \ge \mathcal{L}_{\mathrm{BT}}(\hat r) = \mathcal{L}_{\mathrm{DPO}}(\pi_{\hat r})$. For 2, $\pi^* = \pi_{r^*}$ and $\mathcal{L}_{\mathrm{BT}}(r') = \mathcal{L}_{\mathrm{DPO}}(\pi_{r'}) \ge \mathcal{L}_{\mathrm{DPO}}(\pi^*) = \mathcal{L}_{\mathrm{BT}}(r^*)$ for every $r'$.

The existence hypothesis excludes preference models that are fitted only by sending some reward differences to $\pm\infty$, such as deterministic preferences. The losses involve only prompts with $\rho(x) > 0$ and pairs drawn from $\mu$, so minimizers need not be unique; the statement concerns sets of minimizers. The coincidence of optimizers says nothing about how either procedure behaves with finite data or approximate optimization, and DPO remains an offline method.

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Proposition 4 and its proof (Appendix B), with Section 3.2. [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Sections 4 and 5.1 (the Bradley–Terry case). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
