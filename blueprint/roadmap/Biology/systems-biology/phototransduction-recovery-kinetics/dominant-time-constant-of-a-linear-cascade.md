# Dominant time constant of a linear cascade

Consider a cascade of $n$ first-order low-pass stages, stage $i$ having impulse response $g_i(t) = C_i e^{-t/\tau_i}$ for $t \ge 0$, with distinct time constants $\tau_1 < \tau_2 < \cdots < \tau_n$. Its impulse response, the response $e^*(t) = E^*(t)/\Phi$ of the final enzymatic effector per unit input, is the convolution $e^* = g_1 * g_2 * \cdots * g_n$; with $a_i = 1/\tau_i$ and $C = C_1 \cdots C_n$,

$$e^*(t) = C \sum_{i=1}^{n} \frac{e^{-a_i t}}{\prod_{j \ne i}(a_j - a_i)}, \qquad t \ge 0 .$$

**Theorem.** At long times the stage with the longest time constant dominates: for every $0 < \delta \ll 1$ there is a time $T_\delta$ such that for $t > T_\delta$,

$$e^*(t) = C' e^{-t/\tau_n}\,\big(1 + O(\delta)\big), \qquad C' = \frac{C}{\prod_{j < n}(a_j - a_n)} .$$

## Depends on

- [Recovery translation invariance](recovery-translation-invariance.md)

## Expansion

The partial-fraction form follows by Laplace transform: $\hat e^*(p) = C\prod_i (p + a_i)^{-1}$. Since $a_n < a_i$ for $i < n$, each other term is smaller than the $i = n$ term by a factor $e^{-(a_i - a_n)t}$, so comparing consecutive terms one finds times $T_{i+1}$ beyond which the term in $e^{-a_i t}$ is below any prescribed fraction of the term in $e^{-a_{i+1} t}$; taking $T_\delta$ as the largest of these makes the remainder $O(\delta)$ relative to the leading term. Applied to phototransduction (activated rhodopsin, transducin and phosphodiesterase lifetimes), this shows that the RTI time constant $\tau_c$ is the largest time constant in the cascade up to the effector, and the nonlinear cGMP hydrolysis–synthesis step and the Hill relation preserve it.

## Sources

- S. Nikonov, N. Engheta, E. N. Pugh Jr., "Kinetics of recovery of the dark-adapted salamander rod photoresponse", Journal of General Physiology 111(1) (1998) 7–37, Theorem 2, Theorem 3, and Appendix I (Eqs. A2.1–A2.4), <https://doi.org/10.1085/jgp.111.1.7>, PMCID PMC1887775.
