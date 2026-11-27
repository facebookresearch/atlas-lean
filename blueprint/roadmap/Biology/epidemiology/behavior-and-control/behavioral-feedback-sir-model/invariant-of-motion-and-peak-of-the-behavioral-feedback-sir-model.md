# Invariant of motion and peak of the behavioral-feedback SIR model

**Model.** Susceptible, infected and recovered fractions $(x,y,z)$ on the simplex $x+y+z=1$ evolve by

$$\dot x=-\frac{b(x)}{1+ay}\,xy,\qquad \dot y=\frac{b(x)}{1+ay}\,xy-\gamma y,\qquad \dot z=\gamma y,$$

with recovery rate $\gamma>0$, prevalence sensitivity $a\ge0$, and $b:[0,1]\to(0,\infty)$ differentiable and non-decreasing ($a=0$, $b$ constant is Kermack–McKendrick). Define the reproduction number and its companion

$$R(x,y)=\frac{x\,b(x)}{\gamma(1+ay)},\qquad \rho(x,y)=1-\frac1{R(x,y)},$$

so $\dot y=(R-1)\gamma y$, and $f(x)=x\,b(x)$, which is strictly increasing.

**Basic dynamics.** Solutions are unique and stay in the simplex; $x$ is non-increasing; $y(t)>0$ for all $t$ iff $y(0)>0$; and $(x,y,z)\to(x_\infty,0,1-x_\infty)$. If $R(x_0,y_0)\le1$, $y$ decreases strictly; if $R(x_0,y_0)>1$, $y$ increases up to a unique peak time and then decreases.

**Invariant of motion.** With

$$g(x)=\int_1^x\frac{\gamma a}{s\,b(s)}\,ds,\qquad \psi(x,y)=y\,e^{-g(x)}-\int_1^x e^{-g(s)}\Big(-1+\frac{\gamma}{s\,b(s)}\Big)ds,$$

$\psi$ is differentiable with $\psi_y=e^{-g(x)}$, $\psi_x=e^{-g(x)}\rho(x,y)$, and is constant along solutions.

**Peak.** If $R(x_0,y_0)\le1$ then $y(t)\le y_0$. If $R(x_0,y_0)>1$, the map $\phi(y)=\psi\big(f^{-1}(\gamma(1+ay)),\,y\big)$ is invertible on the relevant range and the peak prevalence is

$$\max_{t\ge0}y(t)=\phi^{-1}\big(\psi(x_0,y_0)\big),$$

attained at a finite time; the peak lies on the curve $R=1$, i.e. $x\,b(x)=\gamma(1+ay)$.

**Control.** For $\dot x=-(1-u)\frac{b(x)}{1+ay}xy$, $\dot y=(1-u)\frac{b(x)}{1+ay}xy-\gamma y$ with control $u\in[0,1]$, the sublevel set of the invariant through $(1-\bar y,\bar y)$ splits the states into those whose uncontrolled peak stays below a capacity $\bar y$ (zero cost) and those that require the minimal intervention holding $y=\bar y$ until $R$ drops to $1$; the cost of that strategy has a closed form as an integral of $\rho(x,\bar y)$.

## Expansion

Along solutions $dy/dx=-1+\gamma(1+ay)/(x\,b(x))$, a linear ODE in $y$ with integrating factor $e^{-g(x)}$; integrating gives $\psi$. At the peak $\dot y=0$, so $R=1$, which pins $x=f^{-1}(\gamma(1+ay))$; evaluating $\psi$ there and using conservation of $\psi$ yields the peak equation. With $a=0$ and $b\equiv\beta$, $g\equiv0$ and $\psi=x+y-\frac\gamma\beta\ln x$, the classical SIR invariant, and the formula reduces to the classical peak.

## Sources

- M. Alutto, L. Cianfanelli, G. Como, F. Fagnani, "Behavioral-feedback SIR epidemic model: analysis and control", *2025 IEEE 64th Conference on Decision and Control (CDC)* (2025), 3615–3621, Section 2 (Lemma 1, Propositions 1–3, Lemma 2), Section 4 (controlled model, Proposition 4), <https://doi.org/10.1109/cdc57313.2025.11312680> (preprint arXiv:2509.12257).
