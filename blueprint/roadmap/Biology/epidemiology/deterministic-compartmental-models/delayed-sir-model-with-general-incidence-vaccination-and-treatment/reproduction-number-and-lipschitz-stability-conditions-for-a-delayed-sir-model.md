# Reproduction number and Lipschitz stability conditions for a delayed SIR model with vaccination and treatment

**Model.** Let $x, y, z$ be susceptible, infected and recovered numbers, with delays $\eta$ (vaccination), $\tau$ (infection) and $\delta$ (treatment):

$$\begin{aligned}
x' &= a - b f(x,y) - dx - c\,v(x(t-\eta)) + \alpha z,\\
y' &= b_1 f(x(t-\tau), y) - r\,p(y) - d_1 y,\\
z' &= r\,p(y(t-\delta)) - \alpha z,
\end{aligned}$$

with positive constants. The incidence $f$, vaccination $v$ and treatment $p$ are nonnegative and $C^1$, $f(0,y) = f(x,0) = 0$, $f$ and $p$ are increasing, and they satisfy two-sided Lipschitz bounds

$$K_1|x-\bar x| + K_2|y-\bar y| \le |f(x,y) - f(\bar x,\bar y)| \le K_3|x-\bar x| + K_4|y-\bar y|,$$

$$M_1|x-\bar x| \le |v(x) - v(\bar x)| \le M_2|x-\bar x|, \qquad L_1|y-\bar y| \le |p(y) - p(\bar y)| \le L_2|y-\bar y|.$$

Typical choices are $f = xy$, $xy/(1+bx)$, $xy/(1+ay)$, $p(y) = y$ or $y/(a+y)$, $v(x) = x$.

**Reproduction number.** With disease-free susceptible level $x^*$, the next-generation matrix is scalar and

$$R_0 = \frac{b_1 f_y(x^*, 0)}{r\,p'(0) + d_1}.$$

**Theorem (local stability).** If $R_0 > 1$ the disease-free equilibrium is unstable. If $R_0 < 1$ it is locally stable provided the treatment-delay condition $\frac{r}{\alpha}e^{-\lambda\delta}\frac{dp(0)}{dy_\delta} < 1$ holds. The endemic equilibrium $(x^*, y^*, z^*)$ is locally asymptotically stable if

$$\frac{b_1}{r p'(y^*) + d_1}\Big(f_y(x^*,y^*) + e^{-\lambda\tau}f_{x_\tau}(x^*,y^*)\Big) < 1 \quad\text{and}\quad \frac{r}{\alpha}e^{-\lambda\delta}\frac{dp(y^*)}{dy_\delta} < 1.$$

**Theorem (global stability without delays).** In the absence of delays, the endemic equilibrium is globally asymptotically stable whenever

$$bK_1 - b_1K_3 + d + cM_1 > 0 \quad\text{and}\quad bK_2 - b_1K_4 + rL_1 + rL_2 + d_1 > 0.$$

Delay-dependent analogues hold under additional inequalities that bound the admissible delays.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

There is a single infected compartment, so the reproduction number is the per-capita infection rate at the disease-free state, $b_1 f_y(x^*,0)$, divided by the per-capita removal rate $r p'(0) + d_1$. The global results use $\ell^1$-type functionals: the norm $|x| + |y| + |z|$ augmented, in the delayed case, by integrals of $|x|$ and $|y|$ over the delay windows $[t-\eta,t]$, $[t-\tau,t]$, $[t-\delta,t]$, and the distance $|x - \bar x| + |y - \bar y| + |z - \bar z|$ between solutions. The two-sided Lipschitz bounds convert each nonlinear term into a multiple of $|x|$ or $|y|$, and the stated parameter inequalities make the upper right Dini derivative negative, which gives boundedness, uniqueness of the equilibrium and attraction to it.

## Sources

- Sushil Pathak and Venkata Ratnam Kota, "An influential study of a time-delayed epidemic model incorporating vaccination and treatment interventions", *Advances in Continuous and Discrete Models* 2025 (2025), 57, <https://doi.org/10.1186/s13662-025-03920-0>. Preprint version: arXiv:2307.00339 (2023), model in Section 2, Theorems 3.1–3.5 (Section 3) and Theorems 4.1–4.2 (Section 4), <https://doi.org/10.48550/arXiv.2307.00339>.
