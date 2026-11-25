# Additive noise models and causal identifiability

Observational data identify a causal graph in general only up to Markov equivalence: with two variables, $X \to Y$ and $Y \to X$ cannot be told apart from the joint law without assumptions on the mechanisms. Restricting the structural equations changes this. In an additive noise model $Y = f(X) + N$ with $N$ independent of $X$, the causal direction is identifiable unless the model is of a special form; for linear $f$ the exception is exactly the Gaussian case, where a backward model $X = \psi Y + \tilde N$ with $\tilde N$ independent of $Y$ exists (LiNGAM, Shimizu et al. 2006; Peters, Mooij, Janzing and Schölkopf 2014, Proposition 13), and for nonlinear $f$ identifiability holds generically (Hoyer et al. 2009). These results are the basis of causal discovery methods that regress each variable on the others and test whether the residuals are independent of the regressors.

## The linear Gaussian case is not identifiable

- [A linear Gaussian additive noise model has a backward model](exists-indep-fun-backward-of-has-gaussia.md)
- [Linear additive noise models with Gaussian laws are reversible](exists-indep-fun-backward-of-map-eq-gaus.md)

## Non-Gaussian noise identifies the direction

- [A reversible linear additive noise model is Gaussian](gaussian-of-indep-fun-backward.md)

## Nonlinear additive noise models

- [Reversible additive noise models satisfy the identifiability differential equation](identifiability-ode-of-reversible.md)

## Related topics

- [Structural causal models and counterfactuals](../structural-causal-models-and-counterfactuals/README.md): structural equations $X_k = f_k(X_{\mathrm{pa}(k)}, U_k)$ with independent disturbances, of which $Y = \varphi X + N$ is the simplest continuous instance.
- [Markov equivalence and Bayesian network scores](../markov-equivalence-and-bayesian-network-scores/README.md): without restrictions on the mechanisms, observational data identify the graph only up to Markov equivalence, and $X \to Y$, $Y \to X$ are Markov equivalent.
