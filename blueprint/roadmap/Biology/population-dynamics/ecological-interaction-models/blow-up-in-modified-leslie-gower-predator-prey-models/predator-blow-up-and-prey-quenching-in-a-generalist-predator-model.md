# Predator blow-up and prey quenching in a generalist-predator model

**Model.** Prey $X(t)\ge0$ grows logistically and suffers a generalized (group-defence) functional response; a generalist predator $Y(t)\ge0$ reproduces sexually, modelled by the modified Leslie–Gower term $Y^2$:

$$\frac{dX}{dt}=RX\Big(1-\frac{X}{K}\Big)-\frac{MXY}{X^p+C},\qquad \frac{dY}{dt}=\Big(D-\frac{E}{X+A}\Big)Y^2,$$

with positive parameters and $p\ge1$ ($p=1$ Holling II, $p=2$ Holling IV, $1<p<2$ Cosner). This is the two-species subsystem of the Upadhyay–Rai food chain.

**Definitions.** A solution *blows up* at $T^*<\infty$ if $|u(t)|\to\infty$ as $t\to T^*$; it *quenches* at $T^{**}<\infty$ if $|du/dt|\to\infty$ as $t\to T^{**}$ while $u$ itself stays finite.

**Theorem.**

1. (Blow-up) For sufficiently large initial data $(X_0,Y_0)$, $Y(t)\to\infty$ at a finite time $T^*$, whatever the parameters; in particular the solutions are not globally bounded, even under parameter conditions previously claimed to give boundedness. Comparison with $\dot Y=DY^2$ gives the lower bound $T^*>1/(DY_0)$.
2. (Quenching at the same time) For such data the prey quenches at a finite time equal to the predator blow-up time: $\lim_{t\to T^*}|dX/dt|=+\infty$ while $X(t)$ tends to a positive finite limit and $Y(t)\to\infty$.
3. (Predator gestation delay restores global existence) If the predator's reproduction is delayed, $\dot Y=DY(t-\tau)^2-\frac{E}{X+A}Y^2$ with $\tau>0$ and positive continuous history on $[-\tau,0]$, then the predator remains bounded on every finite interval, so solutions exist for all time. By contrast, a delay placed only in the prey's logistic term does not prevent blow-up.

## Expansion

Separating variables in the predator equation gives $Y(t)=\big(1/Y_0-\int_0^t(D-E/(X(s)+A))\,ds\big)^{-1}$. If $X_0$ is so large that $X+A>E/D$ on a short interval $[0,\delta)$, the integrand is positive and the denominator reaches $0$ before $\delta$ once $1/Y_0+\delta E/X_0<D\delta$; the intermediate value theorem then yields a finite blow-up time. At blow-up, $X$ does not tend to $0$ (in the paper's argument, $X\to0$ would make the predator growth rate approach $D-E/A<0$, contradicting blow-up), so the predation term $MXY/(X^p+C)$ diverges and $dX/dt\to-\infty$; conversely quenching of $X$ requires $Y\to\infty$, so the two times coincide. With the delay in the reproduction term, on each interval $[k\tau,(k+1)\tau]$ one has $\dot Y\le DY(t-\tau)^2$ with the right side already known and bounded (method of steps), so $Y$ stays bounded step by step.

Locally, the interior equilibrium is asymptotically stable when $C>C_H$ and undergoes a Hopf bifurcation at

$$C_H=\frac{\big(\frac{E}{D}-A\big)^p\,(ADp+AD+DKp-Ep-E)}{E-AD},$$

so bistability between a stable equilibrium or limit cycle (small data) and blow-up (large data) is possible.

## Sources

- Vaibhava Srivastava, Kwadwo Antwi-Fordjour and Rana D. Parshad, "Exploring unique dynamics in a predator–prey model with generalist predator and group defense in prey", Chaos: An Interdisciplinary Journal of Nonlinear Science 34 (2024), 013107, <https://doi.org/10.1063/5.0171950>; numbering as in arXiv:2306.13666: Definitions 1–2, Theorems 3, 4, 5, 6, 8 and 9, Corollary 1, Lemmas 2–3.
