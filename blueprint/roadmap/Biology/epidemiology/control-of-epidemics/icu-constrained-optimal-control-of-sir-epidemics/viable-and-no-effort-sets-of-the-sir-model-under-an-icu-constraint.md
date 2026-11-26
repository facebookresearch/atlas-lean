# Viable and no-effort sets of the SIR model under an ICU constraint

**Setting.** Normalized SIR dynamics with recovery rate $\gamma>0$ evolve in the triangle $\mathbb{T}=\{(s,i)\in\mathbb{R}_+^2:s+i\le1\}$, and the infected fraction must stay below an intensive-care capacity $i_M\in(0,1]$. Two controls are considered.

- *Vaccination:* $s'=-\beta si-v(t)s$, $i'=\beta si-\gamma i$ with measurable $v(t)\in[0,v_M]$.
- *Transmission reduction (lockdown):* $s'=-b(t)si$, $i'=b(t)si-\gamma i$ with measurable $b(t)\in[\beta_*,\beta]$, $0<\beta_*<\beta$.

The *viable set* is the set of initial states from which some control keeps $i(t)\le i_M$ for all $t\ge0$; the *no-effort set* is the set of states from which the uncontrolled trajectory ($v\equiv0$, resp. $b\equiv\beta$) does; the *maximal forward invariant set* is the set from which every control does.

**Theorem.**

1. In both models the maximal forward invariant set equals the no-effort set $A=\{i\le\Gamma_A(s)\}$, where

$$\Gamma_A(s)=\begin{cases} i_M, & s\le\gamma/\beta,\\ i_M-s+\dfrac{\gamma}{\beta}+\dfrac{\gamma}{\beta}\log\Big(\dfrac{\beta s}{\gamma}\Big), & s>\gamma/\beta\end{cases}$$

(truncated at $0$ where this expression becomes negative).

2. Under transmission reduction the viable set is $\{i\le\Phi_B(s)\}$ with the same formula in which $\beta$ is replaced by the strongest admissible reduction $\beta_*$:

$$\Phi_B(s)=\begin{cases} i_M, & s\le\gamma/\beta_*,\\ i_M-s+\dfrac{\gamma}{\beta_*}+\dfrac{\gamma}{\beta_*}\log\Big(\dfrac{\beta_* s}{\gamma}\Big), & s\in(\gamma/\beta_*,s_M^*),\\ 0, & \text{otherwise},\end{cases}$$

where $s_M^*$ is the root of the middle expression.

3. Under vaccination the viable set is $\{i\le\Gamma_B(s)\}$ with $\Gamma_B=i_M$ on $[0,\gamma/\beta]$ and, for $s>\gamma/\beta$, $\Gamma_B(s)=\varphi(s)$, the unique solution $i$ of

$$s+i-\frac{\gamma}{\beta}-i_M+\frac{v_M}{\beta}\log\Big(\frac{i}{i_M}\Big)-\frac{\gamma}{\beta}\log\Big(\frac{\beta s}{\gamma}\Big)=0,$$

that is, the maximal-vaccination trajectory through $(\gamma/\beta,i_M)$.

## Expansion

Infections peak when $s$ crosses the herd immunity level $\gamma/b$, so the binding constraint is at the peak. Along constant controls the SIR model has first integrals: $s+i-\frac{\gamma}{b}\log s$ for transmission $b$, and $s+i+\frac{v_0}{\beta}\log i-\frac{\gamma}{\beta}\log s$ for constant vaccination $v_0$. The boundary of each set is the level curve of the relevant first integral passing through the peak point $(\gamma/b,i_M)$ for the extreme control: the uncontrolled dynamics for $A$, maximal lockdown $\beta_*$ or maximal vaccination $v_M$ for the viable set. A comparison argument shows that no control can do better than the extreme one at keeping the peak below $i_M$, and that no control can push an uncontrolled-safe trajectory above $i_M$, which gives the coincidence of the invariant and no-effort sets.

## Sources

- Florin Avram, Lorenzo Freddi, Dan Goreac, "Optimal Control of a SIR Epidemic With ICU Constraints and Target Objectives", arXiv:2108.10589 (2021): Section 2 (definition of no-effort, all-control and feasible zones; viability theorem with the explicit boundary functions). <https://doi.org/10.48550/arXiv.2108.10589> Published version: Applied Mathematics and Computation 418 (2022) 126816, <https://doi.org/10.1016/j.amc.2021.126816>.
- Matteo Della Rossa, Lorenzo Freddi, Dan Goreac, "Optimality of vaccination for an SIR epidemic with an ICU constraint", arXiv:2407.08425 (2024): Section 2 (existence, uniqueness and first integrals of controlled trajectories), Section 3.1 (viability theorem identifying the maximal forward invariant, no-effort and viable sets). <https://doi.org/10.48550/arXiv.2407.08425> Published version: J Optim Theory Appl 204, 8 (2025), <https://doi.org/10.1007/s10957-024-02598-w>.
