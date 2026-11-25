# Scaled-state switched-to-averaged error bound for the ideal buck

Under the hypotheses of the scaled ideal-buck averaging bound ($L, C, R, I_{\mathrm{ref}}, V_{\mathrm{ref}} > 0$, $T \ge 0$, $\varepsilon > 0$, a duty $d$ with values in $[0,1]$ that is $L_d$-Lipschitz on $[0,T]$, the PWM signal $s$ with cycle length $\varepsilon$, and continuous switched and averaged states $(i, v)$, $(\bar\imath, \bar v)$ satisfying the buck integral equations on $[0,T]$ driven by $s$ and $d$), let $z = (i/I_{\mathrm{ref}}, v/V_{\mathrm{ref}})$ with the sup norm, and

$$\tilde A = \begin{pmatrix} 0 & -V_{\mathrm{ref}}/(L I_{\mathrm{ref}}) \\ I_{\mathrm{ref}}/(C V_{\mathrm{ref}}) & -1/(RC) \end{pmatrix}, \qquad \tilde b = \left(\frac{V_{\mathrm{in}}}{L I_{\mathrm{ref}}}, 0\right).$$

Then for every $t \in [0,T]$,

$$\lVert z(t) - \bar z(t) \rVert_\infty \le e^{\lVert \tilde A \rVert T}\left(\lVert z(0) - \bar z(0) \rVert_\infty + \lVert \tilde b \rVert_\infty\,\varepsilon\left(1 + \frac{L_d T}{2}\right)\right),$$

where $z(0), \bar z(0)$ are the scaled initial values and $\lVert \tilde A \rVert$ is the operator norm for the sup norm.
