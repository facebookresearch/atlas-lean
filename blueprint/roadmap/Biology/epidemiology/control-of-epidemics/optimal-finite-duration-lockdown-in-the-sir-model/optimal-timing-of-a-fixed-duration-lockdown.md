# Optimal timing of a fixed-duration lockdown for the SIR final size

**Setting.** Consider the controlled SIR system

$$\dot S = -u(t) \beta S I, \qquad \dot I = u(t) \beta S I - \gamma I,$$

with $S(0) = S_0$, $I(0) = I_0 > 0$, $S_0 + I_0 \le 1$, basic reproduction number $\mathcal{R}_0 = \beta/\gamma > 1$ and herd-immunity threshold $S_{\mathrm{herd}} = 1/\mathcal{R}_0$. The control $u$ models social distancing; for a maximal lockdown intensity $\alpha \in [0,1)$ and window $[T, T']$ let $\mathcal{U}_{\alpha, T, T'}$ be the controls with $\alpha \le u \le 1$ on $[T, T']$ and $u = 1$ elsewhere. Write $S_\infty(u) = \lim_{t\to\infty} S(t)$, so the final size is $1 - S_\infty(u)$, and let $u_{T, T'} = \mathbf{1}_{[0,T]} + \alpha \mathbf{1}_{[T,T']} + \mathbf{1}_{[T', \infty)}$.

**Invariant.** For $\Phi_{\mathcal{R}}(S, I) = S + I - \mathcal{R}^{-1} \ln S$, along any trajectory $\frac{d}{dt}\Phi_{\mathcal{R}}(S, I) = (\beta u/\mathcal{R} - \gamma) I$; in particular, if $u = 1$ after time $T'$, then $S_\infty(u)$ is the unique solution in $[0, S_{\mathrm{herd}}]$ of $\Phi_{\mathcal{R}_0}(S_\infty, 0) = \Phi_{\mathcal{R}_0}(S(T'), I(T'))$, and $S_\infty(u) \le S_{\mathrm{herd}}$.

**Theorem.** Fix $\alpha \in [0,1)$ and a duration $D > 0$. The problem $\sup_{T \ge 0} \sup_{u \in \mathcal{U}_{\alpha, T, T+D}} S_\infty(u)$ has a unique solution, namely the bang-bang control $u_{T^*, T^*+D}$ (maximal distancing during the whole allowed period). With $(S^T, I^T)$ the solution under $u_{T, T+D}$ and

$$\psi(T) = 1 - \frac{I^T(T+D)}{I^T(T)} + (\alpha - 1)\gamma \int_T^{T+D} \frac{I^T(T+D)}{I^T(t)}\, dt,$$

one has $T^* = 0$ if $\psi(0) \ge 0$, and otherwise $T^*$ is the unique root of $\psi(T^*) = 0$ ($\psi < 0$ on $(0, T^*)$ and $\psi > 0$ afterwards, so bisection finds it). If $T^* > 0$ then $S(T^*) > S_{\mathrm{herd}}$ when $\alpha > 0$ and $S(T^*) = S_{\mathrm{herd}}$ when $\alpha = 0$: the lockdown starts before herd immunity is reached. For fixed $S_0 \in (S_{\mathrm{herd}}, 1)$, $T^* \to \infty$ as $I_0 \to 0^+$. Moreover the optimal value $S^*_\infty$ is strictly increasing in $D$ and strictly decreasing in $\alpha$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The quantity $\Phi_{\mathcal{R}_0}$ is conserved under the uncontrolled flow and decreases at rate $(1-u)\beta I$ under distancing, so the final size is determined by the value of $\Phi_{\mathcal{R}_0}$ at the end of the intervention, and maximizing $S_\infty$ amounts to minimizing it. For a fixed window, the Pontryagin principle and a switching-function analysis show the optimal control is $u = \alpha$ on a subinterval ending at the window's end, and a time-shift argument then shows the optimal control over all windows saturates the whole duration. Differentiating the cost with respect to the start time $T$ (via the sensitivity of $S(T+D)$) yields the function $\psi$, whose sign change locates the unique optimum. Uniqueness of the optimal control gives the strict monotonicity in $D$ and $\alpha$.

## Sources

- Pierre-Alexandre Bliman, Michel Duprez, "How Best Can Finite-Time Social Distancing Reduce Epidemic Final Size?", arXiv (2020). Theorem 1, Theorem 2, Lemma 1, Lemma 2, Theorem 4, Proposition 1, Proposition 3. <https://doi.org/10.48550/arXiv.2009.14648> Published version: Journal of Theoretical Biology 511 (2021) 110557, <https://doi.org/10.1016/j.jtbi.2020.110557>.
