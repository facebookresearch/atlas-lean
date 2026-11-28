# Identifiability of parametric copula models for dependent censoring

In the setting of the [observed-data density](copula-dependent-censoring-observed-density.md), let $F_T \in \{F_{T,\theta_T} : \theta_T \in \Theta_T\}$, $F_C \in \{F_{C,\theta_C} : \theta_C \in \Theta_C\}$ and $\mathcal C \in \{\mathcal C_\theta : \theta \in \Theta\}$ be parametric families. Write $u_t = F_{T,\theta_T}(t)$, $v_t = F_{C,\theta_C}(t)$, and let $\max^*$ denote the maximum over $(\theta, \theta_T, \theta_C) \in \Theta \times \Theta_T \times \Theta_C$. Suppose

- **(C1)** for $a \in \{0, \infty\}$: $\lim_{t \to a} f_{T,\theta_{T1}}(t)/f_{T,\theta_{T2}}(t) = 1$ iff $\theta_{T1} = \theta_{T2}$, and likewise for $f_C$;
- **(C2a)** $\min\{\max^* \lim_{t\to 0} h_{T|C,\theta}(u_t \mid v_t),\ \max^* \lim_{t\to\infty} h_{T|C,\theta}(u_t \mid v_t)\} = 0$;
- **(C2b)** the same with $h_{C|T,\theta}(v_t \mid u_t)$.

**Theorem.** Then the density $f_{Y,\Delta}$ determines $(\theta_T, \theta_C)$, and it determines $\theta$ whenever $\theta \mapsto \mathcal C_\theta(u_t, v_t)$, $t \ge 0$, is injective on $\Theta$ (as for the usual one-parameter families); so the model is identified.

(The source's Theorem 3.1 concludes from (C1) and (C2) alone that "the model is identified", and its proof settles $\theta$ with "since the copula is unique, it follows that $\theta_1=\theta_2$". Uniqueness of the copula (Sklar's theorem) does not give this: $f_{Y,\Delta}$ reveals $\mathcal C_\theta$ only along the curve $t\mapsto(u_t,v_t)$, and even the whole copula cannot separate two parameters that index the same copula. For example, take Frank copulas reparameterized as $\mathcal C_\theta=\mathcal C^{\mathrm{Frank}}_{\theta^2}$ on $\Theta=\mathbb R\setminus\{0\}$ with margins satisfying (C1): (C2) holds as for the Frank family, but $\theta$ and $-\theta$ give the same $f_{Y,\Delta}$, so $\theta$ is not identified. The page therefore adds the injectivity condition on $\theta\mapsto\mathcal C_\theta(u_t,v_t)$.)

(C1) holds for the log-normal, Weibull and log-logistic families. It fails for an unrestricted log-Student-$t$ family: with scale and degrees of freedom fixed, two different log-locations give densities whose ratio at $\log t$ tends to $1$ in both tails, because translated Student densities have asymptotically equal polynomial tails. The theorem itself remains valid for any families satisfying (C1). (C2) holds for the Frank copula for all margins; for the Gumbel copula if $\lim_{t\to0}\log F_{T}(t)/\log F_{C}(t) \in (0, \infty)$ for all marginal parameters; and, for Archimedean generators with $\lim_{v \to 1}\psi'(v) \in (-\infty, 0)$, one has $\lim_{t\to\infty} h_{T|C,\theta}(u_t \mid v_t) = 1$. For the Clayton copula with $\theta > 0$ the model is identified when (C1) holds and $\lim_{t\to0} F_T(t)/F_C(t) \in \{0, +\infty\}$ for all marginal parameters.

## Expansion

By (C2b), at $a = 0$ or $a = \infty$ the factor $1 - h_{C|T}$ in $f_{Y,\Delta}(t, 1)$ tends to $1$, so $\lim_{t \to a} f_{Y,\Delta,\alpha_1}(t, 1)/f_{Y,\Delta,\alpha_2}(t, 1) = \lim_{t\to a} f_{T,\theta_{T1}}(t)/f_{T,\theta_{T2}}(t)$; equality of the observed densities forces this limit to be $1$ and (C1) gives $\theta_{T1} = \theta_{T2}$. Similarly (C2a) identifies $\theta_C$. With both margins known, $F_Y = F_T + F_C - \mathcal C_\theta(F_T, F_C)$ determines $\mathcal C_\theta$ along the curve $t \mapsto (u_t, v_t)$, which pins down $\theta$ under the injectivity hypothesis (the paper's proof appeals to uniqueness of the copula at this step).

## Depends on

- [Observed-data density under copula-dependent censoring](copula-dependent-censoring-observed-density.md)

## Sources

- C. Czado and I. Van Keilegom, "Dependent censoring based on parametric copulas", *Biometrika* (published online 2022), <https://doi.org/10.1093/biomet/asac067>. Theorems 3.1–3.4, Lemma 3.1 and the proofs in the Appendix.
