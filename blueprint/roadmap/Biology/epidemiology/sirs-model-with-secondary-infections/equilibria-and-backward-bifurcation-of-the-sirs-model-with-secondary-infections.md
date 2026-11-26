# Equilibria and backward bifurcation of the SIRS model with secondary infections

**Model.** Split a closed population (normalized to size $1$) into totally susceptible $S$, primary infected $I$, temporarily immune $T$, partially susceptible $P$, secondary infected $Y$ and fully immune $R = 1 - S - I - T - P - Y$. With positive parameters $\beta$ (transmission), $\alpha$ (relative infectiousness of secondary infections), $\nu$ (relative susceptibility of $P$), recovery rates $\gamma_1, \gamma_2$, loss of temporary immunity at rate $\varepsilon$, and loss of partial and full protection both at rate $\delta\varepsilon$ ($0 < \delta, \varepsilon \ll 1$), the reduced system is
$$
\begin{aligned}
S' &= -\beta S(I + \alpha Y) + \delta\varepsilon P, \\
I' &= \beta S(I + \alpha Y) - \gamma_1 I, \\
T' &= \gamma_1 I - \varepsilon T, \\
P' &= \delta\varepsilon + \varepsilon T (1 - \delta) - \nu\beta P (I + \alpha Y) - \delta\varepsilon (S + I + 2P + Y), \\
Y' &= \nu\beta P (I + \alpha Y) - \gamma_2 Y .
\end{aligned}
$$

**Results.**
1. The simplex $\Delta = \{(S, I, T, P, Y) \ge 0 : S + I + T + P + Y \le 1\}$ is forward invariant.
2. The basic reproduction number is $\mathcal{R}_0 = \beta / \gamma_1$; it depends only on the primary flow $S \to I \to T$. The disease-free equilibrium (DFE) is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.
3. *(Global stability.)* If $\gamma_1 \le \gamma_2$, $\mathcal{R}_0 < 1$ and $\alpha\nu < 1/\mathcal{R}_0$, the DFE is globally exponentially stable on $\Delta$.
4. *(Endemic equilibria.)* If $\mathcal{R}_0 > 1$ there is a unique endemic (positive) equilibrium. If $\mathcal{R}_0 < 1$, then for $\delta \approx 0$ there are exactly two endemic equilibria if and only if
$$
\alpha\nu > \frac{\gamma_2}{\gamma_1}
\quad\text{and}\quad
\mathcal{R}_0 > 2\,\frac{\gamma_2}{\gamma_1\alpha\nu}\left(\frac12 - \frac{\gamma_2}{\gamma_1\alpha\nu} + \sqrt{\nu - \frac{\gamma_2}{\gamma_1\alpha}\Bigl(1 - \frac{\gamma_2}{\gamma_1\alpha}\Bigr)}\right).
$$
In that regime endemic states coexist with the locally stable DFE below threshold, the signature of a backward bifurcation at $\mathcal{R}_0 = 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The next-generation computation at the DFE sees only $S$ and $I$, because at the DFE every individual is totally susceptible and $P = Y = 0$, which is why $\mathcal{R}_0$ ignores $\alpha$ and $\nu$. Below threshold, an epidemic that has already built up a large partially susceptible pool can keep itself going through secondary infections when $\alpha\nu$ (infectiousness times susceptibility of the reinfected class, scaled by duration $\gamma_1/\gamma_2$) exceeds $1$; the endemic equilibria then come from a quadratic whose discriminant gives the square-root condition. The global-stability condition $\alpha\nu\mathcal{R}_0 < 1$ bounds the reinfection reproduction number, and between the two conditions there is a gap where neither global stability nor bistability is proved.

## Sources

- P. Kaklamanos, A. Pugliese, M. Sensi, S. Sottile, "A geometric analysis of the SIRS model with secondary infections", arXiv:2304.03793 (2023), Section 2 (model), Propositions 1–2, Lemma 3, Theorems 4–5, Appendix (proof of Theorem 5), <https://doi.org/10.48550/arXiv.2304.03793>.
