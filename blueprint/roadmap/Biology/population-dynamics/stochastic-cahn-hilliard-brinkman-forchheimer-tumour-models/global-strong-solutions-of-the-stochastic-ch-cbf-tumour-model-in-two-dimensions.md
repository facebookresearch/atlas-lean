# Global strong solutions of the stochastic CH-CBF tumour model in two dimensions

Consider the stochastic Cahn–Hilliard–convective Brinkman–Forchheimer tumour model on a bounded smooth domain $\mathcal{O}\subset\mathbb{R}^2$ (velocity $v$, phase field $\phi$, nutrient $\sigma$, multiplicative noise $G_1(v)\,dW_1$ in the momentum equation and $G_2(\sigma)\,dW_2$ in the nutrient equation), under the hypotheses on the potential $\psi$, the proliferation switch $h$, the noise coefficients and the sources stated for the maximal strong solution. Assume in addition that

- the Forchheimer exponent satisfies $r\in[1,3]$;
- $(v_0,\phi_0,\sigma_0)\in L^p(\Omega;\mathcal{H})$, with $\mathcal{H}=L^2_{\rm div}\times H^1\times L^2$, and $(z,u,w)\in L^p(\Omega;L^2_{\rm loc}([0,\infty);V'\times L^2\times(H^1)'))$ for some $p\ge4$ (besides $(v_0,\phi_0,\sigma_0)\in L^2(\Omega;V\times H^2\times H^1)$).

Then the maximal strong solution $\{(v,\phi,\sigma),\{t_n\},\varrho\}$ is global: $\varrho=\infty$ almost surely. Combined with pathwise uniqueness, the two-dimensional stochastic CH-CBF tumour model is globally well posed in $V\times H^2\times H^1$.

## Depends on

- [Maximal strong solutions of the stochastic CH-CBF tumour model](maximal-strong-solutions-of-the-stochastic-ch-cbf-tumour-model.md)

## Expansion

Fix $T<\infty$. It suffices to show $\mathbb{P}(t_n\le T\ \text{for all } n)=0$, i.e. that the $\mathcal{V}$-norm plus the dissipation integral cannot blow up before $T$. In two dimensions the Ladyzhenskaya and Agmon inequalities control the convective terms $(v\cdot\nabla)v$, $(v\cdot\nabla)\phi$, $(v\cdot\nabla)\sigma$ by the energy, which is bounded in $L^p(\Omega)$ for $p\ge4$ by the $p$th-order energy inequality. A stochastic Gronwall lemma then gives a bound on higher-order norms up to stopping times, uniformly in $n$, so the blow-up alternative cannot occur before $T$.

## Sources

- K. Rawat and K. Sakthivel, *Strong Solutions for the Stochastic Cahn-Hilliard Convective Brinkman-Forchheimer Model for Tumor Growth*, arXiv:2605.29779 (2026), <https://doi.org/10.48550/arXiv.2605.29779>. Theorem 5.1 (global existence of strong solutions in 2D); Lemma 4.1 (energy inequality).
