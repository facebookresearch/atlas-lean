# Frequentist risk as the integral of the loss under the law of the estimate

Let $\delta : S \to A$ be a measurable estimator, $(P_\theta)$ a family of probability laws on $S$, $\ell_\theta : A \to [0, \infty)$ losses and $\theta$ a parameter with $a \mapsto \ell_\theta(a)$ measurable. Then the integral of $\ell_\theta$ under the law of $\delta$ under $P_\theta$ (the composition of $P_\theta$ with the deterministic kernel of $\delta$) equals the frequentist risk $\int\ell_\theta(\delta(s))\,dP_\theta(s)$, in $[0, \infty]$.
