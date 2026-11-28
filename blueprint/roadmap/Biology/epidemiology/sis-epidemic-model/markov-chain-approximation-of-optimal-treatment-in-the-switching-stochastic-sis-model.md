# Markov chain approximation of optimal treatment in the switching stochastic SIS model

**Model.** Let $\alpha(t)$ be a continuous-time Markov chain on $\mathcal M=\{1,\dots,m_0\}$ with generator $\Lambda=(\Lambda_{\iota\ell})$, and $w(t)$ an independent standard Brownian motion. The normalized SIS model with regime-switching parameters, white-noise perturbation $\lambda_{\alpha}\to\lambda_\alpha+\sigma_\alpha\dot w$ of the contact rate, and a treatment (or isolation) control $C(t)\ge0$ that raises the recovery rate is

$$dS=\big[\mu_{\alpha}-\lambda_{\alpha}SI+\gamma_{\alpha}I-\mu_{\alpha}S\big]dt-\sigma_{\alpha}SI\,dw,\qquad dI=\big[\lambda_{\alpha}SI-(\mu_{\alpha}+\gamma_{\alpha}+C)I\big]dt+\sigma_{\alpha}SI\,dw,$$

with $\alpha=\alpha(t)$, $C(t)$ taking values in a compact set $\mathcal U\subset[0,\infty)$ containing $0$, and $\mu_\ell$, $\gamma_\ell$, $\lambda_\ell$ nonnegative for each $\ell\in\mathcal M$ (the source's assumption (A)).

**Theorem (well-posedness).** For $(s_0,i_0)\in(0,1)^2$ with $s_0+i_0=1$, any $\ell_0\in\mathcal M$ and constant control $C\equiv c_0\in\mathcal U$, there is a unique global solution with $(S(t),I(t))\in(0,1)^2$ and $S(t)+I(t)=1$ for all $t\ge0$, almost surely. Hence $I$ solves the switching stochastic logistic equation

$$dI=I\big[\lambda_{\alpha}-\mu_{\alpha}-\gamma_{\alpha}-\lambda_{\alpha}I-C\big]dt+\sigma_{\alpha}I(1-I)\,dw .$$

**Control problem.** Fix $\xi\in(0,1)$ below the initial prevalence and let $\tau=\inf\{t\ge0:I(t)\le\xi\}$ be the eradication time. For a bounded, continuous, nonnegative running cost $F$ (for example $F(i,\ell,c)=a_0+a_1i+a_2ic^2$, weighting outbreak duration, burden of infection and treatment cost) and discount $\delta>0$, minimize over adapted controls

$$J(i,\ell,C)=\mathbb E_{i,\ell}\int_0^{\tau}e^{-\delta t}F(I(t),\alpha(t),C(t))\,dt,\qquad V(i,\ell)=\inf_CJ(i,\ell,C).$$

Formally $V$ solves the coupled Hamilton–Jacobi–Bellman system

$$\min_{c\in\mathcal U}\Big[b(i,\ell,c)V_i+\tfrac12a(i,\ell)V_{ii}+\sum_{\iota}\Lambda_{\ell\iota}V(i,\iota)+F(i,\ell,c)-\delta V\Big]=0,\qquad V(\xi,\ell)=0,$$

with $b(i,\ell,c)=i(\lambda_\ell-\mu_\ell-\gamma_\ell-\lambda_\ell i-c)$ and $a(i,\ell)=\sigma_\ell^2i^2(1-i)^2$.

**Theorem (convergence of the approximating chains).** Let $(I^h_n,\alpha^h_n)$ be the controlled Markov chain on $\{kh\}\times\mathcal M$ with

$$Q_h(i,\ell,c)=a(i,\ell)+h|b(i,\ell,c)|-h^2\Lambda_{\ell\ell}+h,\qquad p^h\big((i,\ell),(i\pm h,\ell)\mid c\big)=\frac{a(i,\ell)/2+b(i,\ell,c)^{\pm}h}{Q_h(i,\ell,c)},$$

$$p^h\big((i,\ell),(i,\ell')\mid c\big)=\frac{h^2\Lambda_{\ell\ell'}}{Q_h(i,\ell,c)}\ (\ell'\ne\ell),\qquad p^h\big((i,\ell),(i,\ell)\mid c\big)=\frac{h}{Q_h(i,\ell,c)},\qquad \Delta t^h(i,\ell,c)=\frac{h^2}{Q_h(i,\ell,c)},$$

all other transition probabilities $0$, where $r^+=\max\{r,0\}$ and $r^-=-\min\{r,0\}$ (Section 3.2; locally consistent with the controlled switching diffusion by Lemma 3.1, including $\sup_{n,\omega}|\Delta I^h_n|\to0$ as $h\to0$), and let $V^h$ be its value function, defined by the discrete dynamic programming equation. The source's display of $Q_h$ prints "$a(i,\ell,c)+h|b(i,\ell)|$"; the page writes $a(i,\ell)+h|b(i,\ell,c)|$ because $a$ does not depend on the control and $b$ does, as in the transition probabilities printed directly below it. Then the interpolated processes, together with their drift and martingale parts, relaxed controls and stopping times, are tight, every weak limit solves the controlled switching diffusion with a relaxed control, and

$$V^h(i,\ell)\to V(i,\ell)\qquad (h\to0).$$

The same well-posedness and value-function convergence, for the analogous chain the source constructs in Section 4, hold for the SIS model with vaccination of newborns and susceptibles and waning vaccine immunity, controlled jointly by treatment and the vaccination rates.

## Depends on

- [Solution of the SIS system](is-solution.md)

## Expansion

Positivity and the invariance $S+I=1$ follow from a Lyapunov-type stopping-time argument for the logistic equation with multiplicative noise. The HJB equation need not have a classical solution, so instead of solving it the method of Kushner and Dupuis builds a finite-state controlled Markov chain whose one-step transitions up or down by $h$ have probabilities proportional to $a/2+b^{\pm}h$ and whose regime jumps follow $\Lambda$; its dynamic programming equation is solved by value or policy iteration. Weak convergence of the chains, with controls embedded as relaxed controls so that limits exist, identifies the limit as a solution of the original controlled problem; optimality of the limit and convergence of costs then give $V^h\to V$. Because $F$ is bounded and $\delta>0$, the value is finite even though $\tau$ may be infinite. The numerical examples show feedback treatment policies that switch with the environmental regime.

## Sources

- Ky Tran, George Yin, "Optimal control and numerical methods for hybrid stochastic SIS models", Nonlinear Analysis: Hybrid Systems 41 (2021), 101051, <https://doi.org/10.1016/j.nahs.2021.101051>. Published version of arXiv:2101.03261, cited next; locators there refer to the arXiv version.
- K. Tran and G. Yin, "Optimal control and numerical methods for hybrid stochastic SIS models", arXiv:2101.03261 (2021), Section 2 (model, Theorem 2.1, cost and HJB equation), Section 3 (Markov chain approximation; Theorems 3.5 and 3.6) and Section 4 (vaccination model; Theorems 4.1 and 4.2), <https://doi.org/10.48550/arXiv.2101.03261>.
