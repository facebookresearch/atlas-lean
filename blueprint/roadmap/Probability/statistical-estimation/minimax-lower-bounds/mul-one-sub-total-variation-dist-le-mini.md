# Le Cam's two-point lower bound

Let $P$ be a statistical model, a Markov kernel from a measurable parameter space $\Theta$ to a
sample space $\Omega$, and let $\ell : \Theta \times \Theta \to [0, \infty]$ be a loss, measurable in its
second argument, satisfying the $\alpha$-triangle inequality
$\ell(\theta_0, \theta_1) \le \alpha (\ell(\theta_0, t) + \ell(\theta_1, t))$ with $\alpha \in [0, \infty)$.
For all $\theta_0, \theta_1 \in \Theta$,

$$
\ell(\theta_0, \theta_1)\, \bigl(1 - \mathrm{TV}(P_{\theta_0}, P_{\theta_1})\bigr) \le 2\alpha\, R^*,
\qquad R^* = \inf_{\kappa} \sup_{\theta \in \Theta} \mathbb{E}_{\hat\theta \sim \kappa \circ P_\theta}\, \ell(\theta, \hat\theta),
$$

where $R^*$ is the minimax risk, the infimum running over all randomised
estimators, that is Markov kernels $\kappa$ from $\Omega$ to $\Theta$. For $0 < \alpha < \infty$ the
minimax risk is at least $\ell(\theta_0, \theta_1)(1 - \mathrm{TV}(P_{\theta_0}, P_{\theta_1}))/(2\alpha)$:
an estimation problem is at least as hard as testing between two of its parameters.

Randomisation matters: with no data, $\Theta = \{0, 1\}$ and the 0-1 loss, the minimax risk is
$1/2$, attained only by guessing at random, while every deterministic estimator has worst-case risk
$1$ (Polyanskiy and Wu, Remark 28.4). The proof reduces a randomised estimator $\kappa$ to the
[deterministic bound](mul-one-sub-total-variation-dist-le-two.md) for the identity estimator on
the output laws $\kappa \circ P_{\theta_i}$, whose total variation is at most
$\mathrm{TV}(P_{\theta_0}, P_{\theta_1})$ by the
[data-processing inequality for total variation](../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/total-variation-dist-comp-le-self.md).

## Informally uses

- [Le Cam's two-point lower bound for one deterministic estimator](mul-one-sub-total-variation-dist-le-two.md):
  applied to the identity estimator on the output laws.
- [Data-processing inequality for total variation](../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/total-variation-dist-comp-le-self.md):
  a randomised estimator does not increase total variation.

## Background

- [Contiguity and Le Cam's lemmas](../contiguity-and-le-cam-s-lemmas/README.md):
  Le Cam's asymptotic theory of experiments, the other half of his approach to lower bounds.
- [Fano's inequality](../../../InformationTheory/information-inequalities/fano-s-inequality/fano-inequality.md):
  the information-theoretic route to lower bounds with many hypotheses.

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025, Theorem 31.1, eq. (31.2), with the minimax risk of Section 28.3.2.
