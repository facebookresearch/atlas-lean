# Bayesian estimate minimizes expected missing information

**Controllable Markov chain.** An agent's world is a controllable Markov chain with $N$ states $\mathcal{S}$, $M$ actions $\mathcal{A}$ and kernel $\Theta$, where for each $(a,s)$ the row $\Theta_{as\cdot}\in\Delta_{N-1}$ is the distribution of the next state when action $a$ is taken in state $s$. States are observed directly. The agent holds an internal model $\Phi$ of $\Theta$.

**Missing information.** The inaccuracy of $\Phi$ is

$$I_M(\Theta\,\|\,\Phi) = \sum_{a\in\mathcal{A}}\sum_{s\in\mathcal{S}} D_{\mathrm{KL}}(\Theta_{as\cdot}\,\|\,\Phi_{as\cdot}),\qquad D_{\mathrm{KL}}(\Theta_{as\cdot}\,\|\,\Phi_{as\cdot}) = \sum_{s'}\Theta_{ass'}\log_2\frac{\Theta_{ass'}}{\Phi_{ass'}}.$$

**Theorem.** Let the true kernel be modeled as a random variable $\boldsymbol\Theta$ with prior $f$, and let $\vec d$ be the observed transitions. Then the posterior mean (Bayesian estimate)

$$\hat\Theta := \mathbb{E}_{\boldsymbol\Theta\mid\vec d}[\boldsymbol\Theta]$$

is the unique minimiser over internal models $\Phi$ of the expected missing information:

$$\hat\Theta = \arg\min_\Phi \mathbb{E}_{\boldsymbol\Theta\mid\vec d}\big[I_M(\boldsymbol\Theta\,\|\,\Phi)\big].$$

In particular $\hat\Theta_{ass'} = p(s'\mid a, s, \vec d)$ is the posterior predictive probability of the next transition.

## Expansion

$I_M$ is a sum over independent rows, so each row is minimised separately. Dropping the $\Phi$-independent entropy term,

$$\mathbb{E}\big[D_{\mathrm{KL}}(\boldsymbol\Theta_{as\cdot}\|\Phi_{as\cdot})\big] = \text{const} - \sum_{s'}\mathbb{E}[\boldsymbol\Theta_{ass'}]\log_2\Phi_{ass'},$$

which is the cross-entropy $H\big(\mathbb{E}[\boldsymbol\Theta_{as\cdot}];\Phi_{as\cdot}\big)$, minimised exactly at $\Phi_{as\cdot} = \mathbb{E}[\boldsymbol\Theta_{as\cdot}]$ by Gibbs' inequality. With independent Dirichlet priors on the rows this is the usual add-pseudocount estimator.

## Sources

- D. Y. Little, F. T. Sommer, *Learning and exploration in action-perception loops*, Frontiers in Neural Circuits 7 (2013), 37, Sections 2.1–2.3 (Eqs. 2–5, Theorem 1) and Appendix A1. <https://doi.org/10.3389/fncir.2013.00037> (PMCID: PMC3619626)
