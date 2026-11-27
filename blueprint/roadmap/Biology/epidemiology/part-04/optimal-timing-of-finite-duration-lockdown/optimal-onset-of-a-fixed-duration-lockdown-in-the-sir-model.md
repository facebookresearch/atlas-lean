# Optimal onset of a fixed-duration lockdown in the SIR model

**Model.** Consider the controlled SIR system for population fractions

$$\dot S = -u(t)\, \beta S I, \qquad \dot I = u(t)\, \beta S I - \gamma I, \qquad t \ge 0,$$

with $S(0) = S_0 > 0$, $I(0) = I_0 > 0$, $S_0 + I_0 \le 1$, and $\mathcal{R}_0 = \beta/\gamma > 1$. The input $u(t) \in [\alpha, 1]$ is the relative contact rate ($u = 1$: no restrictions; $u = 0$: complete lockdown), where $\alpha \in [0, 1)$ is the maximal lockdown intensity. Let $S_\infty(u) = \lim_{t \to \infty} S(t)$, so the attack ratio is $S_0 - S_\infty(u)$, and let $S_{\mathrm{herd}} = 1/\mathcal{R}_0$. For a duration $D > 0$ and onset $T \ge 0$, let $\mathcal{U}_{\alpha, T, T+D}$ be the inputs with $\alpha \le u \le 1$ on $[T, T + D]$ and $u = 1$ elsewhere, and let

$$u_{T, T+D} = \mathbf{1}_{[0, T)} + \alpha\, \mathbf{1}_{[T, T + D)} + \mathbf{1}_{[T + D, \infty)}$$

be maximal lockdown on $[T, T+D]$. With $(S_T, I_T)$ the solution under $u_{T, T+D}$, define

$$\psi(T) = 1 - \frac{I_T(T + D)}{I_T(T)} + (\alpha - 1)\, \gamma \int_T^{T + D} \frac{I_T(T + D)}{I_T(t)}\, dt .$$

**Theorem.** For every $\alpha \in [0, 1)$ and $D > 0$, the problem

$$\sup_{T \ge 0}\ \sup_{u \in \mathcal{U}_{\alpha, T, T + D}} S_\infty(u)$$

(minimize the final size using at most $D$ time units of distancing, starting at any time) has a unique solution, the bang-bang input $u_{T^*, T^* + D}$, where

- $T^* = 0$ if $\psi(0) \ge 0$;
- otherwise $T^*$ is the unique root of $\psi(T^*) = 0$, with $\psi < 0$ on $(0, T^*)$ and $\psi > 0$ on $(T^*, \infty)$ (so $T^*$ can be computed by bisection).

Moreover, if $T^* > 0$ then $S(T^*) > S_{\mathrm{herd}}$ when $\alpha > 0$ and $S(T^*) = S_{\mathrm{herd}}$ when $\alpha = 0$: complete lockdown should begin exactly at the epidemic peak, partial lockdown before it. For fixed $S_0 \in (S_{\mathrm{herd}}, 1)$, $T^* \to \infty$ as $I_0 \to 0^+$.

**Monotonicity.** The optimal value $S^*_\infty(\alpha, D)$ is strictly increasing in $D$ and strictly decreasing in $\alpha$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)
- [Limits and final size of the SIR epidemic](../../global-behaviour-of-the-sir-model/tendsto-final-size.md)

## Expansion

Because $u = 1$ after the intervention window, the uncontrolled SIR dynamics then drive $S$ below the herd threshold, $S_\infty(u) \le S_{\mathrm{herd}}$, so minimizing the final size means stopping the outbreak as close as possible to herd immunity. For a fixed window $[T, T+D]$ the optimal input is bang-bang with maximal intensity on a terminal subinterval; optimizing over the onset as well shows that the whole window should be used at intensity $\alpha$, and the first-order condition for the onset is $\psi(T) = 0$, whose sign structure gives uniqueness. Monotonicity follows because enlarging $D$ or lowering $\alpha$ enlarges the admissible set, and equality of optimal values would yield two distinct optimal controls, contradicting uniqueness.

## Sources

- P.-A. Bliman and M. Duprez, "How best can finite-time social distancing reduce epidemic final size?", Journal of Theoretical Biology 511 (2021), 110557, Section 2, Eqs. (1)–(6), Theorems 1 and 2, <https://doi.org/10.1016/j.jtbi.2020.110557> (PMCID: PMC7833531).
