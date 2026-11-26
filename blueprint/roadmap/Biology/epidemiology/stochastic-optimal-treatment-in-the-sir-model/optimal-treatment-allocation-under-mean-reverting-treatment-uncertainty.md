# Optimal treatment allocation under mean-reverting treatment uncertainty

**Model.** In a stochastic SIR model, let $I(t)$ be the infected fraction and let a fraction $\alpha(t)$ of infected individuals receive a treatment (the constraint $\alpha \in [0, 1]$ is relaxed; $\alpha > 1$ can be read as extra doses and $\alpha < 0$ as switching away from a harmful treatment). Untreated infected individuals leave the infected class at recovery rate $K_0$ and death rate $\mu_0$, treated ones at death rate $\mu_1$ and at an uncertain recovery rate $K_1(t)$ modelled as an Ornstein–Uhlenbeck process,

$$dK_1 = \lambda_k(\bar k_1 - K_1)\, dt + \sigma_k\, dB(t), \qquad \lambda_k > 0,$$

and treatment outcomes carry measurement noise $-\alpha I \sigma\, dB(t)$ driven by the same Brownian motion $B$, with $\sigma < 0$ by convention. In the low-infection regime ($S \approx 1$, no transmission noise) the *risk-free infection rate* $r = \beta - K_0 - \mu_0$ is constant, and with the *treatment risk*

$$X(t) = \frac{K_0 + \mu_0 - \mu_1 - K_1(t)}{\sigma}, \qquad \sigma_x = \frac{\sigma_k}{\sigma},$$

the controlled dynamics are

$$dI = \bigl(r + \alpha\sigma X\bigr) I\, dt + \alpha\sigma I\, dB, \qquad dX = \lambda_k(\bar X - X)\, dt - \sigma_x\, dB .$$

A risk-averse decision-maker chooses $\alpha$ to maximize $\mathbb E\bigl[-I(T)^{1-\gamma}/(1-\gamma)\bigr]$ with $\gamma < 0$ (for $\gamma = -1$ this is minimizing $\mathbb E[I(T)^2]$).

**Theorem.** This control problem is the Merton–Wachter problem of portfolio choice with a mean-reverting market price of risk, with $I$ in the role of wealth, $\alpha$ the risky allocation and $X$ the Sharpe ratio. If $\sigma_x < 0$, it has a unique optimal solution. The optimally controlled state is

$$I^*(t) = Z(t)^{1/\gamma}\, H_0\bigl(X(t), T - t\bigr), \qquad \frac{dZ}{Z} = \bigl(r + X^2\bigr) dt + X\, dB, \qquad Z(0) = \Bigl(\frac{I(0)}{H_0(X(0), T)}\Bigr)^{\gamma},$$

with kernel $H_0(X, \tau) = \exp\bigl(\tfrac{1}{\gamma}\bigl(\tfrac12 A_{0,1}(\tau)X^2 + A_{0,2}(\tau)X + A_{0,3}(\tau)\bigr)\bigr)$, and the optimal treatment allocation is

$$\alpha^*(t) = \underbrace{\frac{X(t)}{\gamma\sigma}}_{\text{myopic}} + \underbrace{\frac{\sigma_x}{|\gamma|\sigma}\bigl(A_{0,1}(T-t)\,X(t) + A_{0,2}(T-t)\bigr)}_{\text{hedging}} .$$

Here $A_{0,1}, A_{0,2}, A_{0,3}$ are explicit deterministic functions of the time to go $\tau$: $A_{0,1}$ is the solution of a scalar Riccati equation with $A_{0,1}(0) = 0$, finite for all $\tau \ge 0$ when $\sigma_x < 0$, and $A_{0,2}, A_{0,3}$ are integrals of it.

## Expansion

The key step is the identification with Wachter's exactly solvable portfolio problem: $I$ grows at the risk-free rate $r$ plus $\alpha$ times an excess drift $\sigma X$ with volatility $\alpha\sigma$, and $X$ mean-reverts with shocks perfectly correlated with those of $I$, which makes the market complete. The martingale method then gives $I^* = F(Z, X, t)$ for a PDE whose exponential-quadratic ansatz reduces to Riccati and linear ODEs for $A_{0,1}, A_{0,2}, A_{0,3}$. Wachter proved finiteness of $A_{0,1}$ for $\gamma > 1$; for the risk-averse epidemic objective $\gamma < 0$, the discriminant $\theta_0^2$ of the Riccati equation exceeds $4(|\sigma_x| + \lambda_k)^2$ and its linear coefficient is negative when $\sigma_x < 0$, which keeps $A_{0,1}$ finite. The myopic term is the static mean–variance allocation: it is proportional to $(K_1 + \mu_1 - K_0 - \mu_0)/(|\gamma|\sigma)$, the expected advantage of treatment per unit of outcome noise, and it is optimal when $K_1$ is a constant. The hedging term corrects for the predictable future drift of treatment efficacy and vanishes as $T - t \to 0$. Because the solution is analytic, quantities such as expected treatment deaths can be computed in closed form and used to calibrate the risk-aversion parameter $\gamma$. For moderate infection levels ($S$ not near $1$) the same method gives a perturbative solution with two further kernels.

## Sources

- N. M. Gatto, H. Schellhorn, "Optimal control of the SIR model in the presence of transmission and treatment uncertainty", *Mathematical Biosciences* 333 (2021) 108539, Eqs. (2)–(11), Definition (12)–(15), Proposition 1 and Eq. (20); Proposition 2 for the moderate-infection regime. <https://doi.org/10.1016/j.mbs.2021.108539> (PMC7833871).
- J. A. Wachter, "Portfolio and consumption decisions under mean-reverting returns: an exact solution for complete markets", *Journal of Financial and Quantitative Analysis* 37 (2002) 63–91.
