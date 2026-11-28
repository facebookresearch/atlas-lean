# KL-regularized reward maximization

The KL-regularized reward objective scores a policy by its expected reward minus $\beta$ times its Kullback–Leibler divergence from a fixed reference policy, averaged over prompts. It is the objective of the reinforcement-learning stage of learning from human preferences.

Let $X$ and $Y$ be finite sets of prompts and responses, $\rho$ a probability distribution on $X$, $r : X \times Y \to \mathbb{R}$ a reward, $\pi_{\mathrm{ref}}$ a reference policy and $\beta > 0$. A policy $\pi$ assigns to each prompt $x$ a probability distribution $\pi(\cdot \mid x)$ on $Y$. The KL-regularized reward objective of $\pi$ is

$$J_\beta(\pi) = \mathbb{E}_{x \sim \rho}\Bigl[\mathbb{E}_{y \sim \pi(\cdot \mid x)}\, r(x,y) - \beta\, \mathrm{KL}\bigl(\pi(\cdot \mid x) \,\|\, \pi_{\mathrm{ref}}(\cdot \mid x)\bigr)\Bigr],$$

where $\mathrm{KL}(p \,\|\, q) = \sum_{y \in Y} p(y) \log\bigl(p(y)/q(y)\bigr)$ with the natural logarithm, terms with $p(y) = 0$ equal to $0$, and $\mathrm{KL}(p \,\|\, q) = \infty$ when $p$ charges a response that $q$ does not. Thus $J_\beta(\pi) \in [-\infty, \infty)$, and $J_\beta(\pi) > -\infty$ exactly when $\pi(\cdot \mid x)$ is absolutely continuous with respect to $\pi_{\mathrm{ref}}(\cdot \mid x)$ for every prompt $x$ with $\rho(x) > 0$. Maximizing $J_\beta$ over all policies is the KL-constrained (KL-regularized) reward maximization problem.

## Depends on

- [Kullback–Leibler divergence on a finite space](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

None.

## Expansion

The problem is a one-step, contextual-bandit problem: each prompt receives one response and there are no state transitions. In the standard pipeline of reinforcement learning from human feedback, $r$ is a learned reward model, $\pi_{\mathrm{ref}}$ is the supervised fine-tuned model, and the objective is maximized with a policy-gradient method such as proximal policy optimization; the penalty keeps the policy near the distribution on which the reward model is accurate. Gheshlaghi Azar et al. write $\tau$ for $\beta$ and $D_{\mathrm{KL}}(\pi \,\|\, \pi_{\mathrm{ref}})$ for the $\rho$-average of the per-prompt divergences. The maximizers agree, at every prompt with $\rho(x)>0$, with a closed form, the reference policy tilted by $e^{r/\beta}$; see [the optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md).

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Section 3 (RL fine-tuning phase), equation (3). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Section 2 (finite contexts and actions) and Section 3.1.2, equation (3). [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
