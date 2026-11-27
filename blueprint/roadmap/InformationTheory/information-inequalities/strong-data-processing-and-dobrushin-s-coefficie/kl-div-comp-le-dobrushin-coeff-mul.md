# Strong data-processing inequality for KL divergence

Let $\kappa$ be a Markov kernel between finite sets (with measurable singletons) and $\mu$, $\nu$
probability measures on its input. Then

$$
D(\kappa \circ \mu \,\|\, \kappa \circ \nu) \le \eta_{\mathrm{TV}}(\kappa)\, D(\mu \,\|\, \nu),
$$

that is, the contraction coefficient $\eta_{\mathrm{KL}}(\kappa)$ is at most Dobrushin's
coefficient.
The statement is restricted to finite alphabets, the setting of the cited proof.

## Background

- [Dobrushin's contraction coefficient](dobrushin-coeff.md):
  the coefficient on the right.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 33.6(a) with `f(x) = x log x`; J. E. Cohen, J. H. B. Kemperman and G. Zbăganu (1998).
