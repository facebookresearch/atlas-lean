# Each FRAPPE EM step does not decrease the admixture log-likelihood

Let $I$ and $J$ be finite, $J$ and $K$ nonempty, and let $g$ be a [polymorphic](polymorphic.md) genotype matrix. Then for all [admixture parameters](params.md) $\theta$, $\ell_g(\theta) \le \ell_g(T\theta)$, where $\ell_g$ is the [admixture log-likelihood](admixture-log-lik.md) and $T$ the [FRAPPE EM step](em-step.md).
