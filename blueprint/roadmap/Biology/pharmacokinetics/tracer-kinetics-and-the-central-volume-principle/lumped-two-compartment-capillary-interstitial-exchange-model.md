# Lumped two-compartment capillary–interstitial exchange model

Let a tissue region contain a well-mixed capillary compartment of volume $V_1 > 0$ and a well-mixed interstitial compartment of volume $V_2 > 0$, with tracer concentrations $c_1(t)$ and $c_2(t)$, blood flow $F > 0$, arterial input concentration $c_{\mathrm{aif}}(t)$, and passive exchange with permeability–surface area product $PS > 0$:

$$V_1 \frac{dc_1}{dt} = F\big(c_{\mathrm{aif}}(t) - c_1(t)\big) + PS\big(c_2(t) - c_1(t)\big), \tag{6}$$

$$V_2 \frac{dc_2}{dt} = PS\big(c_1(t) - c_2(t)\big), \tag{7}$$

with $c_1(0) = c_2(0) = 0$. Let $q(t) = V_1 c_1(t) + V_2 c_2(t)$ be the tracer content of the region and $R_F$ its response to a unit impulse $c_{\mathrm{aif}} = \delta$.

1. $dq/dt = F\,(c_{\mathrm{aif}} - c_1)$: the region obeys Fick's mass balance with outflow concentration $c_1$.
2. $R_F(0^+) = F$, in agreement with the central volume principle.
3. The system matrix

$$\begin{pmatrix} -(F + PS)/V_1 & PS/V_1 \\ PS/V_2 & -PS/V_2 \end{pmatrix}$$

has two distinct negative real eigenvalues, so $R_F$ is a sum of two decaying exponentials that start decaying immediately after $t = 0$.
4. $\int_0^\infty R_F(t)\, dt = V_1 + V_2$, so the mean transit time is $(V_1 + V_2)/F$.

## Depends on

- [Central volume principle](central-volume-principle.md)

## Expansion

Adding (6) and (7) cancels the exchange terms and gives property 1. An impulse deposits the amount $F$ in the capillary compartment at $t = 0^+$ ($V_1 c_1(0^+) = F$) and none in the interstitium, so $q(0^+) = F$. The matrix has negative trace and determinant $F \cdot PS / (V_1 V_2) > 0$. Rescaling the coordinates by $\sqrt{V_1}$ and $\sqrt{V_2}$ makes it symmetric, so its eigenvalues are real, and they are distinct because the off-diagonal entries are non-zero. For a unit step input the steady state is $c_1 = c_2 = 1$, so the steady content is $V_1 + V_2$, which equals the integral of the impulse response. Unlike a spatially distributed model, the lumped model has no initial plateau in $R_F$. With an extracellular contrast agent the late signal mainly reflects $V_1 + V_2$, so the vascular volume is poorly identifiable, and first-pass studies focus on estimating $F$.

## Sources

- M. Jerosch-Herold, "Quantification of myocardial perfusion by cardiovascular magnetic resonance", Journal of Cardiovascular Magnetic Resonance 12 (2010) 57, Figure 3, section on model-based analysis, "Central Volume Principle", and Appendix A, Eqs. (6) and (7), <https://doi.org/10.1186/1532-429x-12-57> (PMC2964700).
