# Equality of plasma and interstitial-fluid AUC under passive exchange

Let $C_P(t) \ge 0$ be the free drug concentration in plasma and $C_{ISF}(t)$ the free concentration at a site in the interstitial fluid (ISF), $t \ge 0$. Assume that the drug is not eliminated locally in the tissue, that plasma and ISF are the only relevant compartments, and that exchange is passive with a constant rate constant $k_D > 0$:

$$\frac{dC_{ISF}}{dt} = k_D\,\big(C_P(t) - C_{ISF}(t)\big), \qquad C_{ISF}(0) = 0 .$$

Define the areas under the curves

$$AUC_{plasma} = \int_0^\infty C_P(t)\,dt, \qquad AUC_{ISF} = \int_0^\infty C_{ISF}(t)\,dt .$$

If $AUC_{plasma}$ is finite, then $AUC_{ISF} = AUC_{plasma}$. The value of $k_D$ only changes how fast the ISF exposure accumulates, not its total: the ISF profile is a delayed, smoothed copy of the plasma profile with the same integral.

## Expansion

The solution with a drug-free start is the convolution $C_{ISF} = g * C_P$ with $g(t) = k_D e^{-k_D t}$ for $t \ge 0$. Since $g \ge 0$ and $\int_0^\infty g = 1$, Tonelli's theorem gives $\int_0^\infty C_{ISF} = \int_0^\infty g \cdot \int_0^\infty C_P = AUC_{plasma}$. Equivalently, integrating the ODE over $[0, t]$ gives $C_{ISF}(t) = k_D\big(\int_0^t C_P - \int_0^t C_{ISF}\big)$, and $C_{ISF}(t) \to 0$ along a sequence as $t \to \infty$ because it is integrable. This is Theorem 1 of the source, whose proof is in its Supporting Information. The practical consequence is that total plasma exposure can be read off a single ISF sensor if it records long enough, even when the ISF peak concentration underestimates the plasma peak.

## Sources

- M. K. Erdal, T. E. Kippin, J. P. Hespanha, K. W. Plaxco, Methods of estimating plasma pharmacokinetics from minimally invasive, high temporal resolution measurements of interstitial fluid drug concentrations, Clin. Transl. Sci. 18 (2025), e70248, Theorem 1 and Eq. (1). <https://doi.org/10.1111/cts.70248> (PMCID: PMC12224287)
