# Assouad's lemma

Let $P$ be a statistical model, a Markov kernel from a measurable parameter space $\Theta$ to a sample space $\Omega$, and $\ell : \Theta \times \Theta \to [0, \infty]$ a loss, measurable in its second argument, satisfying the $\alpha$-triangle inequality $\ell(\theta_0, \theta_1) \le \alpha (\ell(\theta_0, t) + \ell(\theta_1, t))$ for all $\theta_0, \theta_1, t$, with $\alpha \in [0, \infty)$. Let $d \in \mathbb{N}$, let $\theta_b \in \Theta$ be parameters indexed by $b \in \{0, 1\}^d$, let $\beta \in [0, \infty]$ with $\ell(\theta_b, \theta_{b'}) \ge \beta\, d_H(b, b')$ for all $b, b'$, where $d_H$ is the Hamming distance, and let $\tau \in \mathbb{R}$ with $\mathrm{TV}(P_{\theta_b}, P_{\theta_{b'}}) \le \tau$ whenever $d_H(b, b') = 1$. Then

$$\beta\, d\, \max(1 - \tau, 0) \le 4\alpha\, R^*, \qquad R^* = \inf_{\kappa} \sup_{\theta \in \Theta} \mathbb{E}_{\hat\theta \sim \kappa \circ P_\theta}\, \ell(\theta, \hat\theta),$$

in $[0, \infty]$ with $0 \cdot \infty = 0$, where $R^*$ is the minimax risk, the infimum running over all randomised estimators, that is Markov kernels $\kappa$ from $\Omega$ to $\Theta$. For $0 < \alpha < \infty$ the minimax risk is therefore at least $\beta\, d\, \max(1 - \tau, 0)/(4\alpha)$. Compared with [Le Cam's two-point bound](mul-one-sub-total-variation-dist-le-mini.md), the bound grows linearly with the dimension $d$ of the cube while only neighbouring hypotheses need to be close.

A randomised estimator $\kappa$ is reduced to the [deterministic bound](mul-one-sub-le-four-mul-i-sup.md) for the identity estimator on the output laws $\kappa \circ P_\theta$, whose neighbours stay within total variation $\tau$ by the [data-processing inequality for total variation](../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/total-variation-dist-comp-le-self.md).

## Informally uses

- [Assouad's lemma for one deterministic estimator](mul-one-sub-le-four-mul-i-sup.md):
  applied to the identity estimator on the output laws.
- [Data-processing inequality for total variation](../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/total-variation-dist-comp-le-self.md):
  a randomised estimator keeps neighbouring hypotheses within $\tau$.

## Background

- [Le Cam's two-point lower bound](mul-one-sub-total-variation-dist-le-mini.md):
  the case of two hypotheses.

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025, Theorem 31.2, eq. (31.5), with $\tau$ bounding the maximum there and the minimax risk of Section 28.3.2.
