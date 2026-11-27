# Naive reproduction number bias under a change in the reporting fraction

Let $M_0, M_1, \dots, M_T \ge 0$ be observed case counts and $q_0,\dots,q_T > 0$ the reporting fractions, so that the true counts are $M_t/q_t$. Compare the naive estimator, which ignores reporting, with the reporting-corrected estimator of the thinned Poisson renewal likelihood with a known serial interval $p = (p_1,\dots,p_k)$:

$$\hat R_0 = \frac{\sum_{t=1}^{T} M_t}{\sum_{t=1}^{T}\sum_{j=1}^{\min(k,t)} p_j M_{t-j}}, \qquad \tilde R_0 = \frac{\sum_{t=1}^{T} M_t/q_t}{\sum_{t=1}^{T}\sum_{j=1}^{\min(k,t)} p_j M_{t-j}/q_{t-j}},$$

assuming all denominators are positive.

**Proposition 1 (constant reporting).** If $q_t = q$ for all $t$, then $\hat R_0 = \tilde R_0$.

**Proposition 2 (one change in reporting).** Take the branching-process case $p_1 = 1$, so $\hat R_0 = \sum_{t=1}^T M_t / \sum_{t=1}^T M_{t-1}$. Let $1 \le t_c < T$, $q_t = q_1$ for $t \le t_c$ and $q_t = q_2$ for $t > t_c$, and put $A = \sum_{t=1}^{t_c} M_t$, $B = \sum_{t=t_c+1}^{T} M_t$, $C = \sum_{t=0}^{t_c} M_t$, $D = \sum_{t=t_c+1}^{T-1} M_t$, $r = q_2/q_1$. Then

$$\tilde R_0 - \hat R_0 = \frac{(1-r)\,\left(M_T A + M_0 B\right)}{(C+D)(rC+D)}.$$

Hence, whenever $M_T A + M_0 B > 0$:
- if $q_1 < q_2$ (reporting improves), $\hat R_0 > \tilde R_0$: the naive estimate overestimates $R_0$;
- if $q_1 > q_2$ (reporting deteriorates, or early over-reporting), $\hat R_0 < \tilde R_0$: the naive estimate underestimates $R_0$.

## Depends on

- [Thinned Poisson renewal likelihood with a reporting fraction](thinned-poisson-renewal-likelihood-with-a-reporting-fraction.md)

## Expansion

With constant $q$, the factor $1/q$ cancels between numerator and denominator of $\tilde R_0$, giving Proposition 1: a uniform under-reporting rate is invisible to the ratio estimator. For Proposition 2, multiply numerator and denominator of $\tilde R_0$ by $q_2$: since the denominator index $t-1 \le t_c$ exactly when $t \le t_c+1$, one gets $\tilde R_0 = (rA+B)/(rC+D)$, while $\hat R_0 = (A+B)/(C+D)$. Cross-multiplying, the numerator of the difference is $(r-1)(AD - BC)$, and $C = M_0 + A$, $D = B - M_T$ give $AD - BC = -(A M_T + B M_0)$. Intuitively, when ascertainment improves partway through, late counts are inflated relative to early ones, which mimics faster growth. The same direction appears in simulations with general serial intervals, and the serial-interval mean is biased as well. Applied to the 2009 La Gloria influenza A/H1N1 outbreak, a reporting fraction rising logistically from 0.4 to 0.9 moved estimates of $R_0$ by up to about a third.

## Sources

- Laura F. White, Marcello Pagano, "Reporting errors in infectious disease outbreaks, with an application to Pandemic Influenza A/H1N1", *Epidemiologic Perspectives & Innovations* 7:12 (2010), Methods, Equation (3), Propositions 1 and 2, and Appendix (proofs of Propositions 1 and 2). <https://doi.org/10.1186/1742-5573-7-12>. PMCID: PMC3018365.
