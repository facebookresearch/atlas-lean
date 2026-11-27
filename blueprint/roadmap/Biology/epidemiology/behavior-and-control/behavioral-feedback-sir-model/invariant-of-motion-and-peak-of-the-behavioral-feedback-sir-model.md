# Invariant of motion and peak of the behavioral-feedback SIR model

**Model.** Susceptible, infected and recovered fractions $(x,y,z)$ on the simplex $x+y+z=1$ evolve by

$$\dot x=-\frac{b(x)}{1+ay}\,xy,\qquad \dot y=\frac{b(x)}{1+ay}\,xy-\gamma y,\qquad \dot z=\gamma y,$$

with recovery rate $\gamma>0$, prevalence sensitivity $a\ge0$, and $b:[0,1]\to(0,\infty)$ differentiable and non-decreasing ($a=0$, $b$ constant is Kermack–McKendrick). Define the reproduction number and its companion

$$R(x,y)=\frac{x\,b(x)}{\gamma(1+ay)},\qquad \rho(x,y)=1-\frac1{R(x,y)},$$

so $\dot y=(R-1)\gamma y$, and $f(x)=x\,b(x)$, which is strictly increasing.

**Basic dynamics.** Solutions are unique and stay in the simplex; $x$ is non-increasing; $y(t)>0$ for all $t$ iff $y(0)>0$; and $(x,y,z)\to(x_\infty,0,1-x_\infty)$. If $y_0>0$ and $R(x_0,y_0)\le1$, $y$ decreases strictly; if $y_0>0$ and $R(x_0,y_0)>1$, $y$ increases strictly up to a peak time $\hat t>0$ and decreases strictly afterwards. (At $y_0=0$, $y\equiv0$ whatever $R(x_0,0)$ is.)

**Invariant of motion.** With

$$g(x)=\int_1^x\frac{\gamma a}{s\,b(s)}\,ds,\qquad \psi(x,y)=y\,e^{-g(x)}-\int_1^x e^{-g(s)}\Big(-1+\frac{\gamma}{s\,b(s)}\Big)ds,$$

$\psi$ is differentiable with $\psi_y=e^{-g(x)}$, $\psi_x=e^{-g(x)}\rho(x,y)$, and is constant along solutions.

**Peak.** Let $y_0>0$. If $R(x_0,y_0)\le1$ then $y(t)\le y_0$ for all $t\ge0$. If $R(x_0,y_0)>1$, put $y_a=1$ when $a=0$ and $y_a=\min\{1,(f(1)-\gamma)/(a\gamma)\}$ when $a>0$; then $f^{-1}(\gamma(1+ay))$ is defined for $y\in(0,y_a]$, the map $\phi(y)=\psi\big(f^{-1}(\gamma(1+ay)),\,y\big)$ on $(0,y_a]$ is invertible, and the peak prevalence is

$$\max_{t\ge0}y(t)=\phi^{-1}\big(\psi(x_0,y_0)\big),$$

attained at a finite time; the peak lies on the curve $R=1$, i.e. $x\,b(x)=\gamma(1+ay)$.

**Control.** For $\dot x=-(1-u)\frac{b(x)}{1+ay}xy$, $\dot y=(1-u)\frac{b(x)}{1+ay}xy-\gamma y$ with control $u\in[0,1]$, fix a capacity $\bar y\in(0,1)$ with $R(1-\bar y,\bar y)>1$, let $\bar x$ solve $\bar x\,b(\bar x)=\gamma(1+a\bar y)$ (so $R(\bar x,\bar y)=1$), and split $D_{\bar y}=\{(x,y):y\le\bar y\}$ into

$$D^-_{\bar y}=\{(x,y)\in D_{\bar y}: R(x,y)\le1,\ y=0,\ \text{or}\ \psi(x,y)\le\psi(\bar x,\bar y)\},\qquad D^+_{\bar y}=D_{\bar y}\setminus D^-_{\bar y}$$

(for $R>1$ and $y>0$, $\psi(x,y)\le\psi(\bar x,\bar y)$ is $\phi^{-1}(\psi(x,y))\le\bar y$, since $\phi(\bar y)=\psi(\bar x,\bar y)$ and $\phi'=e^{-g}>0$). $D^-_{\bar y}$ is positively invariant for the uncontrolled model, whose peak then stays below $\bar y$; from every state of $D^+_{\bar y}$ the uncontrolled prevalence exceeds $\bar y$. The feedback policy that uses no control below the capacity and $u=\rho(x,\bar y)$ on $y=\bar y$, which holds $y=\bar y$ until $x$ reaches $\bar x$, is feasible, costs $0$ on $D^-_{\bar y}$, and on $D^+_{\bar y}$ costs

$$J(x_0,y_0)=\frac1{\gamma\bar y}\int_{\bar x}^{h(x_0,y_0)}\rho(x,\bar y)\,dx,$$

where $h(x_0,y_0)\in(\bar x,1-\bar y]$ is the susceptible fraction when the uncontrolled solution first reaches $y=\bar y$. Whether this policy is optimal is left open by the source.

## Expansion

Along solutions $dy/dx=-1+\gamma(1+ay)/(x\,b(x))$, a linear ODE in $y$ with integrating factor $e^{-g(x)}$; integrating gives $\psi$. At the peak $\dot y=0$, so $R=1$, which pins $x=f^{-1}(\gamma(1+ay))$; evaluating $\psi$ there and using conservation of $\psi$ yields the peak equation. With $a=0$ and $b\equiv\beta$, $g\equiv0$ and $\psi=x+y-\frac\gamma\beta\ln x$, the classical SIR invariant, and the formula reduces to the classical peak.

## Sources

- M. Alutto, L. Cianfanelli, G. Como, F. Fagnani, "Behavioral-feedback SIR epidemic model: analysis and control", *2025 IEEE 64th Conference on Decision and Control (CDC)* (2025), 3615–3621, Section 2 (Lemma 1, Propositions 1–3, Lemma 2), Section 3 (Lemmas 3–6), Section 4 (controlled model, policy (33)–(34), Proposition 4), <https://doi.org/10.1109/cdc57313.2025.11312680> (preprint arXiv:2509.12257).
