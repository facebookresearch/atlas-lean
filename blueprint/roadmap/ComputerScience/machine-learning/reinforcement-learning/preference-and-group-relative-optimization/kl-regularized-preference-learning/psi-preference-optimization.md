# Ψ-preference optimization

Ψ-preference optimization (ΨPO) maximizes the expected value of a non-decreasing transform Ψ of preference probabilities against a fixed comparison policy, minus a KL penalty to a reference policy. Taking Ψ to be the identity gives identity preference optimization (IPO).

Let $X$ and $Y$ be finite sets of contexts and actions, $\rho$ a distribution on $X$, $\mu$ a behavior policy, $p^*(y \succ y' \mid x) \in [0,1]$ the probability that a rater prefers $y$ to $y'$ given $x$, $\pi_{\mathrm{ref}}$ a reference policy and $\tau > 0$. Write $p^*(y \succ \mu \mid x) = \mathbb{E}_{y' \sim \mu(\cdot \mid x)}\, p^*(y \succ y' \mid x)$. For a non-decreasing $\Psi : [0,1] \to \mathbb{R}$ the **ΨPO objective** is

$$\max_\pi\ \mathbb{E}_{x \sim \rho,\ y \sim \pi(\cdot \mid x),\ y' \sim \mu(\cdot \mid x)}\Bigl[\Psi\bigl(p^*(y \succ y' \mid x)\bigr)\Bigr] - \tau\, \mathbb{E}_{x \sim \rho}\, \mathrm{KL}\bigl(\pi(\cdot \mid x) \,\|\, \pi_{\mathrm{ref}}(\cdot \mid x)\bigr),$$

with $y$ and $y'$ independent. It is [KL-regularized reward maximization](kl-regularized-reward-maximization.md) with $\beta = \tau$ and reward $g(x,y) = \mathbb{E}_{y' \sim \mu(\cdot \mid x)} \Psi(p^*(y \succ y' \mid x))$. For $\Psi$ the identity it becomes the **IPO objective**

$$\max_\pi\ p^*_\rho(\pi \succ \mu) - \tau\, \mathbb{E}_{x \sim \rho}\, \mathrm{KL}\bigl(\pi(\cdot \mid x) \,\|\, \pi_{\mathrm{ref}}(\cdot \mid x)\bigr), \qquad p^*_\rho(\pi \succ \mu) = \mathbb{E}_{x \sim \rho,\ y \sim \pi(\cdot \mid x)}\, p^*(y \succ \mu \mid x),$$

the regularized total preference of $\pi$ over $\mu$.

## Depends on

- [KL-regularized reward maximization](kl-regularized-reward-maximization.md)

## Proof depends on

None.

## Expansion

Because the objective is KL-regularized maximization of the reward $g$, its maximizers are the policies agreeing with $\pi^*(y \mid x) \propto \pi_{\mathrm{ref}}(y \mid x) \exp\bigl(\tau^{-1} g(x,y)\bigr)$ at every prompt with $\rho(x)>0$ ([optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)). The objective is stated directly in terms of pairwise preferences, without assuming that they come from pointwise rewards. With the logit $\Psi(q) = \log(q/(1-q))$ and Bradley–Terry preferences it recovers the objectives optimized by reward modeling with KL-regularized maximization and by DPO ([theorem](rlhf-and-dpo-as-psi-preference-optimization.md)); this $\Psi$ is unbounded, which Gheshlaghi Azar et al. identify as the source of weak regularization when preferences are nearly deterministic, and which motivates the bounded choice $\Psi(q) = q$. IPO is then optimized from data through the [IPO loss](identity-preference-optimization-loss.md).

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Section 2 (notation, $p^*(y \succ \mu \mid x)$ and total preference), Section 4, equations (6) and (7), and Section 5, equations (8) and (9). [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
