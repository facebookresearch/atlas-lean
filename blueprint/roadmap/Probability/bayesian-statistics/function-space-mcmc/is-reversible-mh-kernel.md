# Metropolis–Hastings with a prior-reversible proposal is reversible for the posterior

Let $\mu_0$ be a probability measure, $Q$ a Markov kernel reversible with respect to $\mu_0$ and $\Phi$
measurable. Then the Metropolis–Hastings kernel with acceptance probability
$a(u, v) = \min\{1, e^{\Phi(u) - \Phi(v)}\}$ satisfies detailed balance with respect to the posterior
$\mu \propto e^{-\Phi} \mu_0$.

The proof is that of Dashti and Stuart: $e^{-\Phi(u)} a(u, v) = \min\{e^{-\Phi(u)}, e^{-\Phi(v)}\}$ is
symmetric in $(u, v)$, and prior reversibility makes the joint law $\mu_0(du) Q(u, dv)$ symmetric; the
rejection part is supported on the diagonal and is symmetric automatically. The statement
needs neither positivity of the normalising constant nor any topology on the state space; when
$Z = 0$ or $e^{-\Phi}$ is not integrable, the posterior is the zero measure and the statement is vacuous.

## Background

- [The Metropolis–Hastings kernel is reversible](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/is-reversible-mh-kernel.md):
  the finite-state Metropolis–Hastings algorithm with general proposals, where the acceptance ratio
  involves the proposal densities.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Theorem 5.8 (via Theorem 5.7).
