# Delta score for potency shift and its vanishing in a sham combination

Keep the normalized Hill parameterization $y_j(x) = \dfrac{(x/m_j)^{\lambda_j}}{1 + (x/m_j)^{\lambda_j}}$ of the single agents and fix a dose pair $(x_1, x_2)$. Fit the observed combination response in the two centric ways, allowing the potency and shape of one agent to shift in the presence of the other:

$$y_c^{1 \leftarrow 2} = y_2(x_2) + \bigl(1 - y_2(x_2)\bigr)\frac{(x_1/m_{1 \leftarrow 2})^{\lambda_{1 \leftarrow 2}}}{1 + (x_1/m_{1 \leftarrow 2})^{\lambda_{1 \leftarrow 2}}}, \qquad y_c^{2 \leftarrow 1} = y_1(x_1) + \bigl(1 - y_1(x_1)\bigr)\frac{(x_2/m_{2 \leftarrow 1})^{\lambda_{2 \leftarrow 1}}}{1 + (x_2/m_{2 \leftarrow 1})^{\lambda_{2 \leftarrow 1}}} .$$

**Definition (delta score).** With parameter set $\theta = \{m_1, m_2, m_{1 \leftarrow 2}, m_{2 \leftarrow 1}, \lambda_1, \lambda_2, \lambda_{1 \leftarrow 2}, \lambda_{2 \leftarrow 1}\}$ estimated from the dose–response matrix,

$$\delta(\theta) \;=\; \frac{\bigl(y_c^{1 \leftarrow 2} - y_{\mathrm{ZIP}}\bigr) + \bigl(y_c^{2 \leftarrow 1} - y_{\mathrm{ZIP}}\bigr)}{2},$$

where $y_{\mathrm{ZIP}}$ is the [zero interaction potency reference](zip-reference-equals-bliss-of-hill-curves.md). Values $\delta > 0$, $\delta = 0$ and $\delta < 0$ are read as synergy, zero interaction and antagonism; a whole dose–response matrix is summarized by $\Delta = \frac{1}{n} \sum_{i=1}^{n} \delta_i$ over its $n$ interior dose pairs.

**Theorem (sham combination).** If the two agents are one and the same drug, so that $m_1 = m_2 = m_{1 \leftarrow 2} = m_{2 \leftarrow 1}$ and $\lambda_1 = \lambda_2 = \lambda_{1 \leftarrow 2} = \lambda_{2 \leftarrow 1}$, then $\delta = 0$ at every dose pair.

## Depends on

- [The zero interaction potency reference is Bliss independence of the fitted Hill curves](zip-reference-equals-bliss-of-hill-curves.md)

## Remarks

The score measures a shift in potency rather than a gap between two effect levels: if the companion drug only raises the baseline, the fitted $m_{1 \leftarrow 2}, \lambda_{1 \leftarrow 2}$ reproduce $m_1, \lambda_1$ and both bracketed differences vanish. For the sham case, substituting the common parameters makes $y_c^{1 \leftarrow 2}$ the same function of $(x_1, x_2)$ as $y_{\mathrm{ZIP}}$, since with $A = (x_1/m)^{\lambda}$ and $B = (x_2/m)^{\lambda}$ both equal $(A + B + AB)/\bigl((1+A)(1+B)\bigr)$, and likewise for the drug-2-centric term; hence each difference, and so $\delta$, is zero. Dose addition has the same self-consistency property, so the potency-shift score inherits the main argument for the dose-addition reference while remaining defined, through its Bliss-type closed form, on dose pairs where the dose-addition reference does not exist.

## Sources

- B. Yadav, K. Wennerberg, T. Aittokallio and J. Tang, "Searching for drug synergy in complex dose–response landscapes using an interaction potency model", Computational and Structural Biotechnology Journal 13 (2015), 504–513, Section 2.3, Eqs. (17)–(19) and Appendix A2, <https://doi.org/10.1016/j.csbj.2015.09.001>, PMCID: PMC4759128.
