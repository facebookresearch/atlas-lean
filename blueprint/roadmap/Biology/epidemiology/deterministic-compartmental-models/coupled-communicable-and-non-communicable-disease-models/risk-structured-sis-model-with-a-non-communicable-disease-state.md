# Risk-structured SIS model with a non-communicable disease state

Healthy susceptibles $S$ develop a non-communicable condition at rate $a$ and become weakened susceptibles $W$; they return at rate $b$. Both groups catch an SIS infection with different transmission coefficients, and infecteds recover into $S$ or $W$:

$$
S'=-aS+bW-\beta_SSI+\gamma_SI,\qquad W'=aS-bW-\beta_WWI+\gamma_WI,\qquad I'=\beta_SSI+\beta_WWI-\gamma I,
$$

with $\gamma=\gamma_S+\gamma_W$ and constant total population $N=S+W+I$. Solutions are bounded and the non-negative cone is forward invariant. The communicable-disease-free equilibrium is

$$
E_0^*=\Big(\frac{b}{a+b}N,\ \frac{a}{a+b}N,\ 0\Big),
$$

and the basic reproduction number is

$$
R_0=\frac{b\beta_S+a\beta_W}{(a+b)(\gamma_S+\gamma_W)}\,N .
$$

$E_0^*$ is locally asymptotically stable for $R_0<1$ and unstable for $R_0>1$. Unlike the homogeneous SIS model, where $R_{0,S}=\beta_SN/\gamma_S$ is a sharp global threshold, the risk structure created by the non-communicable disease can make the bifurcation at $R_0=1$ subcritical (backward). Endemic equilibria can then exist for $R_0<1$. Ignoring the non-communicable dynamics and fitting a homogeneous SIS model overestimates the reproduction number.

## Proof sketch

At $I=0$ the $(S,W)$ subsystem is a two-state linear exchange with equilibrium $(bN,aN)/(a+b)$. Linearizing the $I$ equation there gives growth rate $\beta_SS_0^*+\beta_WW_0^*-\gamma$, which is negative exactly when $R_0<1$. The source states the two stability cases of its Proposition 2 in reversed order; the linearization above fixes the correct direction. Backward bifurcation arises because recovery redistributes individuals between the $S$ and $W$ classes in proportions $\gamma_S:\gamma_W$ that differ from the disease-free split $b:a$.

## Related topics

- [SIS epidemic model](../../sis-epidemic-model/README.md)

## Sources

- M. Marvá, E. Venturino and M.C. Vera, "A Minimal Model Coupling Communicable and Non-Communicable Diseases", *Mathematical Modelling of Natural Phenomena* 18 (2023), 23, <https://doi.org/10.1051/mmnp/2023026>. Preprint version: arXiv:2303.15928 (2023), Section 2 (system (eq:model), Eqs. (eq:SIS), (eq:R0sis)), Section 3 (Propositions 1–2, Eqs. (eq:W0), (eq:r0)), <https://doi.org/10.48550/arXiv.2303.15928>.
