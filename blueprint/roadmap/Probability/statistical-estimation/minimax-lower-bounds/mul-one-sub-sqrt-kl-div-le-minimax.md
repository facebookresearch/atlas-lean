# Le Cam's two-point bound with Pinsker's inequality

Under the hypotheses of [Le Cam's two-point lower bound](mul-one-sub-total-variation-dist-le-mini.md) ($P$ a Markov kernel from a measurable $\Theta$ to $\Omega$, $\ell$ measurable in its second argument with the $\alpha$-triangle inequality, $\alpha \in [0, \infty)$), for all $\theta_0, \theta_1 \in \Theta$ with $D(P_{\theta_0} \,\|\, P_{\theta_1}) < \infty$,

$$\ell(\theta_0, \theta_1)\, \max\Bigl(1 - \sqrt{D(P_{\theta_0} \,\|\, P_{\theta_1})/2},\ 0\Bigr) \le 2\alpha\, R^*,$$

where $R^*$ is the minimax risk over randomised estimators and the Kullback–Leibler divergence uses the natural logarithm. This is how the two-point method is used in practice: the divergence of $n$ i.i.d. observations is $n$ times that of one, so choosing $\theta_0, \theta_1$ with $D \asymp 1/n$ gives rates of estimation.

## Informally uses

- [Pinsker's inequality, square-root form](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/total-variation-dist-le-sqrt-kl-div.md):
  replaces total variation by the divergence.
- [Le Cam's two-point lower bound](mul-one-sub-total-variation-dist-le-mini.md):
  the bound in total variation.

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025, Theorem 31.1 combined with Pinsker's inequality, Theorem 7.10, as in Section 31.1.
