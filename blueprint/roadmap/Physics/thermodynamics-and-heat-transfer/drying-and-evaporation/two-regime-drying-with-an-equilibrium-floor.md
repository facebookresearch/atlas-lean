# Two-regime drying with an equilibrium floor

Fix a water activity with equilibrium moisture content $X_{\mathrm{eq}} \ge 0$ and first let $X_0 > X_c > X_{\mathrm{eq}}$ and
$m_s, A, N_c, k_d > 0$. Let the moisture content follow the constant-rate law $X' = -A N_c/m_s$ until it reaches the critical value
$X_c$ at $t_c = m_s (X_0 - X_c)/(A N_c)$, and the falling-rate law $X' = -k_d (X - X_{\mathrm{eq}})$ afterwards. The resulting
continuous piecewise solution is $X(t) = X_{\mathrm{eq}} + (X_c - X_{\mathrm{eq}}) e^{-k_d (t - t_c)}$ for $t \ge t_c$, which stays
above $X_{\mathrm{eq}}$. For this positive switching time $t_c>0$, the derivative is continuous at $t_c$ if and only if
$k_d (X_c-X_{\mathrm{eq}})=A N_c/m_s$.

For $X_{\mathrm{eq}}\le X_0\le X_c$, use only $X(t)=X_{\mathrm{eq}}+(X_0-X_{\mathrm{eq}})e^{-k_d t}$ for $t\ge0$.
In particular $X_0=X_c$ has no interior switch and requires no matching with an unused constant-rate slope;
$X_0=X_{\mathrm{eq}}$ is constant. Initial moisture below equilibrium is outside this drying-only statement.
The constant and linear falling-rate laws are stipulated empirical models; the cited source describes the drying regimes, not these exact rate constants.

## Depends on

## Proof depends on

## Sources

- *AENG 252* (drying and storage engineering), Lecture 5, drying rate periods, critical and equilibrium moisture content, <http://eagri.org/eagri50/AENG252/lec14.html>.
