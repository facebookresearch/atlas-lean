# Derivative of the Poisson log-likelihood

Let $\iota$ be a finite index set, $V$ a real normed space, $E_i : V \to \mathbb{R}$ functions and $\psi \in V$ such that each $E_i$ is differentiable at $\psi$ with $E_i(\psi) > 0$. Then for all counts $k$, the map $\phi \mapsto \ell(E(\phi), k)$ is differentiable at $\psi$ with derivative

$$\sum_{i \in \iota} \Bigl(\frac{k_i}{E_i(\psi)} - 1\Bigr) DE_i(\psi),$$

where $\ell$ is the [Poisson log-likelihood](../../../Probability/statistical-estimation/likelihood-and-maximum-likelihood-estimators/poisson-log-lik.md).
