# Mean-field microtubule length model with length-dependent catastrophe

**Model.** A neuron (or dendrite) contains $N$ microtubules (MTs) sharing a fixed tubulin pool $T_{\mathrm{tot}}$. Let $L(t)$ be the mean MT length and $g^\pm(t) \in [0,1]$ the fractions of plus and minus ends in the growing state. Growth at speed $v_g^\pm$ is limited by free tubulin $T_{\mathrm{tot}} - NL$ through Michaelis–Menten kinetics with half-saturation $F_{1/2}$; shrinking ends retract at speed $v_s^\pm$; ends rescue (shrink $\to$ grow) at constant rates $\lambda_{s \to g}^\pm$ and undergo catastrophe (grow $\to$ shrink) at the length-dependent rate

$$
\max\left(\lambda_{\min},\ \lambda_{g \to s}^\pm + \gamma L_0\, \phi\!\left(\frac{L}{L_0}\right)\right),
$$

where $L_0 > 0$ is a characteristic length, $\gamma \ge 0$ the strength of length dependence, $0 < \lambda_{\min} < \lambda^\pm_{g \to s}$, and the shape function $\phi$ is continuous and non-decreasing with $\phi(0) = -1$, $\phi(1) = 0$, $\phi'(1) = 1$ (in practice $\phi(x) = x - 1$). The mean-field system is

$$
\begin{aligned}
\frac{dL}{dt} &= \big(v_g^+ g^+ + v_g^- g^-\big)\frac{T_{\mathrm{tot}} - NL}{F_{1/2} + T_{\mathrm{tot}} - NL} - \Big(v_s^+(1 - g^+) + v_s^-(1 - g^-)\Big)\, \psi_\alpha\!\left(\frac{L}{L_{\mathrm{crit}}}\right),\\
\frac{dg^\pm}{dt} &= (1 - g^\pm)\,\lambda_{s \to g}^\pm - g^\pm \max\left(\lambda_{\min},\ \lambda_{g \to s}^\pm + \gamma L_0\, \phi\!\left(\frac{L}{L_0}\right)\right),
\end{aligned}
$$

where $\psi_\alpha : \mathbb{R}_+ \to [0,1]$ is increasing and $C^1$ with $\psi_\alpha(0) = 0$ and $\psi_\alpha(x) \to 1$ as $x \to \infty$; it approximates the fraction of shrinking MTs that have not yet reached zero length. A Weibull length distribution with shape $\alpha \ge 1$ gives $\psi_\alpha(x) = \exp\left(-\left(\Gamma(1 + 1/\alpha)/x\right)^\alpha\right)$, with $L_{\mathrm{crit}} = v_s^+ \ln 2/\lambda_{s \to g}^+$ the median plus-end shrinkage run.

**Proposition.** After nondimensionalizing lengths by $L_0$ and time by $1/\lambda^+_{s \to g}$, write $\ell = L/L_0$, $\tilde T = T_{\mathrm{tot}}/L_0$, $\ell_0 = 1$ for the scaled characteristic length and $\eta^\pm = \gamma L_0/\lambda^\pm_{g \to s}$. Suppose $\eta^\pm \ge 0$, $\tilde T > N\ell_0$, and all other nondimensional constants are positive, and let $\mathcal{O} = (0, \tilde T/N) \times (0,1) \times (0,1)$. Then for every initial condition $(\ell, g^+, g^-) \in \mathcal{O}$ there is a unique global solution, $\overline{\mathcal{O}}$ is forward invariant, and there is a unique steady state $(\ell_*, g_*^+, g_*^-)$ in $\mathcal{O}$.

## Expansion

On every face of the box the vector field points inward: at $g^\pm = 0$ the rescue term is positive, at $g^\pm = 1$ the catastrophe rate is at least $\lambda_{\min} > 0$, at $\ell = 0$ there is growth but no loss ($\psi_\alpha(0) = 0$), and at $\ell = \tilde T/N$ free tubulin is exhausted. With Lipschitz right-hand sides this gives global existence and uniqueness. For the steady state, each $g^\pm$ balances at

$$
g_*^\pm(\ell) = \frac{1}{1 + \max\left(\tilde\lambda_{\min},\ \big(1 + \eta^\pm \phi(\ell/\ell_0)\big)\lambda^\pm\right)},
$$

which decreases in $\ell$ because $\phi$ is non-decreasing; here $\lambda^\pm = \lambda^\pm_{g \to s}/\lambda^\pm_{s \to g}$ and $\tilde\lambda_{\min} = \lambda_{\min}/\lambda^+_{s \to g}$. Substituting into the length equation leaves $h_1(\ell) = h_0(\ell)$ with $h_1$ (tubulin-limited growth) positive at $0$, vanishing at $\tilde T/N$ and decreasing, and $h_0$ (shrinkage) vanishing at $0$ and increasing; the intermediate value theorem gives exactly one crossing. The steady state's asymptotic stability is supported numerically but not proved. Biologically, length-dependent catastrophe together with a limited tubulin pool is a minimal mechanism that sets a preferred MT length.

## Sources

- Anna C. Nelson, Melissa M. Rolls, Maria-Veronica Ciocanel, Scott A. McKinley, "Minimal Mechanisms of Microtubule Length Regulation in Living Cells", Bulletin of Mathematical Biology 86 (2024), 58, <https://doi.org/10.1007/s11538-024-01279-z>. Published version of arXiv:2310.13666, cited next; locators there refer to the arXiv version.
- Anna C. Nelson, Melissa M. Rolls, Maria-Veronica Ciocanel, Scott A. McKinley, "Minimal Mechanisms of Microtubule Length Regulation in Living Cells," arXiv 2023. Definition 2.1 (length-dependent catastrophe), Definitions 3.1 and 3.2 (active-MT proportion function and mean-field ODE), Proposition 3.3 (global well-posedness and unique steady state). <https://doi.org/10.48550/arXiv.2310.13666>
