# A reversible linear additive noise model is Gaussian

**A reversible linear additive noise model is Gaussian** (Peters, Mooij, Janzing and
Schölkopf, *Causal discovery with continuous additive noise models*, JMLR 15 (2014), the "only
if" direction of Proposition 13, after Shimizu et al. 2006). Let $X$ and $N$ be independent
measurable real random variables on a probability space, neither almost surely constant, and let
$Y = \varphi X + N$ with $\varphi \ne 0$. If there is $\psi \in \mathbb{R}$ such that
$\tilde N = X - \psi Y$ is independent of $Y$, then $X$ and $N$ have nondegenerate Gaussian laws.

In causal terms: from the joint law of $(X, Y)$ alone, the direction $X \to Y$ of a linear structural equation with independent noise can be recovered unless both the cause and the noise are Gaussian; together with the converse ([the linear Gaussian case](exists-indep-fun-backward-of-has-gaussia.md)) this is the characterization of Proposition 13. Peters et al. present it (Section 2.3) among the restrictions of structural equation models that make the graph identifiable, before turning to nonlinear additive noise models, whose bivariate identifiability (Hoyer et al. 2009) is their Theorem 20. The proof they point to uses the Darmois–Skitovich theorem: if two linear combinations of independent random variables, all of whose coefficients are nonzero, are independent, then the variables are Gaussian.

The statement assumes $X$ and $N$ not almost surely constant; Proposition 13 tacitly works with nondegenerate variables. The assumption is needed for both: if $X$ is almost surely constant, $\psi = 0$ gives a backward model for every law of $N$, and if $N$ is almost surely constant, $\psi = 1/\varphi$ makes $X - \psi Y = -N/\varphi$ constant, a backward model for every law of $X$.

## Background

- [Cramér's decomposition theorem](../../../../Probability/characteristic-functions/cramer-decomposition.md): a related characterization of the Gaussian law by independence; the proof here uses instead the Darmois–Skitovich theorem.
