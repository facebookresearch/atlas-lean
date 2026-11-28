# Entrainment and detachment monotonicity of the MFALK

**Entrainment.** Let all rates $\lambda_i(t), \gamma_i(t), \alpha_i(t), \beta_i(t)$ of the [MFALK](mfalk-model-and-its-globally-attracting-steady-state.md) be nonnegative, uniformly bounded and $T$-periodic, and satisfy uniform versions of its two-sided persistence hypothesis (P): there is $c > 0$ with $\lambda_i(t) + \beta_{i+1}(t) > c$ and $\gamma_i(t) + \alpha_{i+1}(t) > c$ for all $i$ and $t$, or $\lambda_i(t) > c$ for all $i$ and $t$, or $\gamma_i(t) > c$ for all $i$ and $t$; and let $\lambda_i(t) + \gamma_i(t) > c$ for $i = 1, \dots, n-1$ and all $t$. Then there is a unique $T$-periodic function $\phi:\mathbb{R}_+ \to \operatorname{int}(C^n)$ such that $x(t,a) - \phi(t) \to 0$ for every initial condition $a \in C^n$; in particular the output rate converges to the $T$-periodic function $(\lambda_n + \gamma_n + \beta_n + \alpha_n)\phi_n - \gamma_n - \beta_n$. A single periodically varying rate, with all others constant, already entrains the whole chain.

**Monotonicity.** The constant-rate MFALK is cooperative: if $a \le b$ componentwise then $x(t,a) \le x(t,b)$ for all $t \ge 0$, strictly in every component for $t > 0$ when $a \ne b$, provided $\lambda_i + \gamma_i > 0$ for $i = 1,\dots,n-1$ and the persistence hypothesis (P) of the MFALK page holds. Under these hypotheses, which give a unique steady state $e \in \operatorname{int}(C^n)$ with output rate $R$,

$$\frac{\partial e_i}{\partial \alpha_j} < 0,\qquad \frac{\partial e_i}{\partial \beta_j} > 0\qquad\text{for all } i, j,$$

and $\partial R/\partial\alpha_j < 0$, $\partial R/\partial \beta_j > 0$ for every site $j < n$. In the translation interpretation, ribosome drop-off from any site lowers the steady-state density everywhere, and drop-off from any site before the last always reduces the output rate $R$ (drop-off at the last site, counted in $R$, can raise it). The source states these results under its one-sided condition, which does not give persistence.

## Expansion

Contraction with a uniform rate holds for the time-varying system under the uniform bounds, and a contractive $T$-periodic system maps the cube into itself by the period map, which is a contraction with a unique fixed point; its trajectory is the periodic attractor. Cooperativity follows from the nonnegative off-diagonal Jacobian entries on the cube. Increasing a detachment rate decreases the vector field componentwise, so by the comparison principle the trajectory, and hence its limit $e$, decreases; irreducibility makes the decrease strict in every component, and the sign of the change in $R$ follows from its expression in $x_n$ together with the steady-state flux balance.

## Depends on

- [MFALK model and its globally attracting steady state](mfalk-model-and-its-globally-attracting-steady-state.md)

## Sources

- Zarai Y, Margaliot M, Tuller T, "A deterministic mathematical model for bidirectional excluded flow with Langmuir kinetics", PLoS One (2017), Eqs. (21)–(23), Theorem 1, Propositions 6–7 and the ribosome drop-off application, <https://doi.org/10.1371/journal.pone.0182178>, PMCID PMC5568237.
