# Global stability and Hopf bifurcation in a delayed stem-cell model

**Model.** Hematopoietic stem cells are proliferating ($P$) or resting ($N$); both die at rate $\delta$; resting cells enter proliferation at rate $\beta(S)$, which depends on the total stem-cell population $S=P+N$; a proliferating phase lasts $\tau$ and ends with division into two resting cells. Then

$$\frac{dS}{dt}=-\delta S(t)+e^{-\delta\tau}\beta\bigl(S(t-\tau)\bigr)N(t-\tau),$$

$$\frac{dN}{dt}=-\delta N(t)-\beta\bigl(S(t)\bigr)N(t)+2e^{-\delta\tau}\beta\bigl(S(t-\tau)\bigr)N(t-\tau),$$

with $\beta$ positive, decreasing and tending to zero (e.g. a Hill function). Nonnegative data give nonnegative global solutions.

**Steady states.** If $(2e^{-\delta\tau}-1)\beta(0)>\delta$, there are exactly two steady states, $E^0=(0,0)$ and $E^*=(S^*,N^*)$ with $(2e^{-\delta\tau}-1)\beta(S^*)=\delta$ and $N^*=(2e^{-\delta\tau}-1)e^{\delta\tau}S^*$; otherwise $E^0$ is the only one.

**Theorem (extinction).** If $(2e^{-\delta\tau}-1)\beta(0)\le\delta$, every solution converges to $(0,0)$: $E^0$ is globally asymptotically stable and the stem-cell population dies out. If the inequality is reversed, $E^0$ is unstable.

**Theorem (Hopf bifurcation).** Assume the existence condition in the form (9): $\delta<\beta(0)$ and $0\le\tau<\bar\tau:=\frac1\delta\ln\frac{2\beta(0)}{\delta+\beta(0)}$. Let $\chi(y)=y\beta'(y)$ and assume (H1) $\chi$ is decreasing on $[0,\beta^{-1}(\delta)]$ and (H2) $\chi(\beta^{-1}(\delta))<-4\delta$. Then there is a unique $\tau^*\in(0,\bar\tau)$ such that $B(\tau)<-A(\tau)$ exactly for $\tau\in[0,\tau^*)$, where the characteristic equation at $E^*$ is $\lambda+A(\tau)-B(\tau)e^{-\lambda\tau}=0$ with

$$A(\tau)=\delta+\beta(S^*(\tau)),\qquad B(\tau)=\big[2\beta(S^*(\tau))+N^*(\tau)\beta'(S^*(\tau))\big]e^{-\delta\tau}.$$

Define, for $\tau\in[0,\tau^*)$,

$$Z_0(\tau)=\tau-\frac{\arccos\big(A(\tau)/B(\tau)\big)}{\sqrt{B(\tau)^2-A(\tau)^2}} .$$

1. If $Z_0$ has no root in $[0,\tau^*)$, $E^*$ is locally asymptotically stable for every $\tau\in[0,\bar\tau)$.
2. If $\tau_c\in(0,\tau^*)$ is the smallest positive root of $Z_0$, $E^*$ is locally asymptotically stable for $\tau\in[0,\tau_c)$, and a Hopf bifurcation occurs at $\tau=\tau_c$ provided that $B(A^2+A'+AA'\tau_c)-B^3-B^2B'\tau_c-B'A\ne0$, with $A,B,A',B'$ evaluated at $\tau_c$.

## Expansion

The quantity $(2e^{-\delta\tau}-1)\beta(0)/\delta$ is the reproduction number of a resting cell at low density: it enters proliferation at rate $\beta(0)$, survives the cycle with probability $e^{-\delta\tau}$, and returns two daughters, one of which replaces it. Because the coefficients of the characteristic equation at $E^*$ depend on $\tau$ (through $S^*$), the stability switch analysis uses the Beretta–Kuang method. The periodic solutions are a model for cyclical neutropenia and other periodic hematological diseases.

## Sources

- Fabien Crauste, "Global Asymptotic Stability and Hopf Bifurcation for a Blood Cell Production Model", arXiv:0904.2495 (2009), Section 2 (model and Proposition 2.1), Propositions 4.1–4.2, Lemmas 5.1–5.3, Proposition 5.1 and Theorem 5.1, <https://doi.org/10.48550/arXiv.0904.2495>.
