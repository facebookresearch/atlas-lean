# Assouad's lemma for one deterministic estimator

Let $(P_\theta)_{\theta \in \Theta}$ be probability measures on $\Omega$ and $\ell : \Theta \times \Theta \to [0, \infty]$ a loss with $\ell(\theta_0, \theta_1) \le \alpha (\ell(\theta_0, t) + \ell(\theta_1, t))$ for all $\theta_0, \theta_1, t$, where $\alpha \in [0, \infty]$. Let $d \in \mathbb{N}$, let $\theta_b \in \Theta$ be parameters indexed by $b \in \{0, 1\}^d$, let $\beta \in [0, \infty]$ with $\ell(\theta_b, \theta_{b'}) \ge \beta\, d_H(b, b')$ for all $b, b'$, where $d_H$ is the Hamming distance, and let $\tau \in \mathbb{R}$ with $\mathrm{TV}(P_{\theta_b}, P_{\theta_{b'}}) \le \tau$ whenever $d_H(b, b') = 1$. Then every deterministic estimator $T : \Omega \to \Theta$ for which each loss $\omega \mapsto \ell(\theta, T(\omega))$ is measurable satisfies

$$\beta\, d\, \max(1 - \tau, 0) \le 4\alpha \sup_{\theta \in \Theta} \mathbb{E}_{P_\theta}\, \ell(\theta, T),$$

in $[0, \infty]$ with $0 \cdot \infty = 0$, the expectations being integrals of $[0, \infty]$-valued functions.

The proof follows Polyanskiy and Wu. A [measurable nearest vertex](exists-measurable-argmin.md) $\hat b$ of $T$ satisfies $\beta\, d_H(\hat b, b) \le 2\alpha\, \ell(\theta_b, T)$ for every $b$. Averaging over the uniform prior on the cube and splitting $d_H$ over coordinates, each coordinate $i$ contributes, for every pair $b$, $b \oplus e_i$, a sum of two error probabilities of the test $\{\hat b_i \ne b_i\}$, which is at least $1 - \tau$ by the [two-point testing bound](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/one-sub-total-variation-dist-le-add-comp.md).

## Informally uses

- [Measurable choice of a minimiser](exists-measurable-argmin.md):
  the projection of the estimator to the cube.
- [Two-point testing bound](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/one-sub-total-variation-dist-le-add-comp.md):
  bounds each coordinate's error.

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025, Theorem 31.2, eq. (31.5), and its proof.
