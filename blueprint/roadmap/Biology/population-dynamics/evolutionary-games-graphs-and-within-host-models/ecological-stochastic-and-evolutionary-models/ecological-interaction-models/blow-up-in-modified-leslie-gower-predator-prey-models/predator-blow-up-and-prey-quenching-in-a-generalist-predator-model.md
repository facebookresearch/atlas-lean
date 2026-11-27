# Predator blow-up and prey quenching in a generalist-predator model

**Model.** Prey $X(t)\ge0$ grows logistically and suffers a generalized (group-defence) functional response; a generalist predator $Y(t)\ge0$ reproduces sexually, modelled by the modified Leslie–Gower term $Y^2$:

$$\frac{dX}{dt}=RX\Big(1-\frac{X}{K}\Big)-\frac{MXY}{X^p+C},\qquad \frac{dY}{dt}=\Big(D-\frac{E}{X+A}\Big)Y^2,$$

with positive parameters and $p\ge1$ ($p=1$ Holling II, $p=2$ Holling IV, $1<p<2$ Cosner). This is the two-species subsystem of the Upadhyay–Rai food chain.

**Definitions.** A solution *blows up* at $T^*<\infty$ if $|u(t)|\to\infty$ as $t\to T^*$; it *quenches* at $T^{**}<\infty$ if $|du/dt|\to\infty$ as $t\to T^{**}$ while $u$ itself stays finite.

**Theorem.**

1. (Blow-up) If $D>E/A$, then for all initial data with $X_0\ge0$, $Y_0>0$, $Y(t)\to\infty$ at a finite time $T^*$ with $1/(DY_0)<T^*\le 1/\big((D-E/A)Y_0\big)$; in particular the solutions are not globally bounded. If $D<E/A$, no solution blows up.
2. (Prey at the blow-up time) If $D>E/A$ and $X_0>0$, then $X(t)\to0$ as $t\to T^*$. With $\kappa=M/\big(C(D-E/A)\big)$, $X(t)=(T^*-t)^{\kappa+o(1)}$, so the prey quenches at $T^*$ ($|dX/dt|\to+\infty$) if $\kappa<1$, and $dX/dt\to0$ if $\kappa>1$.
3. (Predator gestation delay restores global existence) If the predator's reproduction is delayed, $\dot Y=DY(t-\tau)^2-\frac{E}{X+A}Y^2$ with $\tau>0$ and positive continuous history on $[-\tau,0]$, then the predator remains bounded on every finite interval, so solutions exist for all time. By contrast, when $D>E/A$, a delay placed only in the prey's logistic term does not prevent blow-up.

*Note on the source.* The source states blow-up for sufficiently large data whatever the parameters, and a positive finite limit of $X$ at the blow-up time. Both fail: with $D=0.5$, $E=A=0.2$ (the source's Remark 1) one has $D<E/A$ and no blow-up, and at any blow-up time $X\to0$. Items 1–2 state the corrected mathematics, derived in the Expansion.

## Expansion

Separating variables in the predator equation gives $Y(t)=\big(1/Y_0-F(t)\big)^{-1}$ with $F(t)=\int_0^t g$, $g=D-E/(X+A)$. If $D>E/A$, then $g\ge D-E/A>0$, so $F$ reaches $1/Y_0$ by time $1/((D-E/A)Y_0)$, while $g<D$ gives $T^*>1/(DY_0)$. Blow-up forces $\int_0^{T^*}Y=\infty$; since $X$ stays bounded, $(\log X)'\le R-MY/(X^p+C)$ then drives $X\to0$. So $g(t)\to D-E/A$ at a blow-up time, and $F$ cannot increase to $1/Y_0$ there if $D<E/A$, which rules out blow-up in that case. For $D>E/A$, $1/Y=(D-E/A)(T^*-t)(1+o(1))$, and $(\log X)'=-(M/C)Y(1+o(1))+O(1)$ integrates to the stated power law; $dX/dt=-(M/C)XY(1+o(1))$ then gives the quenching dichotomy. With the delay in the reproduction term, on each interval $[k\tau,(k+1)\tau]$ one has $\dot Y\le DY(t-\tau)^2$ with the right side already known and bounded (method of steps), so $Y$ stays bounded step by step.

Locally, the interior equilibrium is asymptotically stable when $C>C_H$ and undergoes a Hopf bifurcation at

$$C_H=\frac{\big(\frac{E}{D}-A\big)^p\,(ADp+AD+DKp-Ep-E)}{E-AD},$$

so bistability between a stable equilibrium or limit cycle (small data) and blow-up (large data) is possible.

## Sources

- Vaibhava Srivastava, Kwadwo Antwi-Fordjour and Rana D. Parshad, "Exploring unique dynamics in a predator–prey model with generalist predator and group defense in prey", Chaos: An Interdisciplinary Journal of Nonlinear Science 34 (2024), 013107, <https://doi.org/10.1063/5.0171950>; numbering as in arXiv:2306.13666: Definitions 1–2, Theorems 3, 4, 5, 6, 8 and 9, Corollary 1, Lemmas 2–3.
