# The zero interaction potency reference is Bliss independence of the fitted Hill curves

Consider two drugs whose single-agent dose–effect curves are Hill curves normalized to $E_{\min} = 0$ and $E_{\max} = 1$,

$$y_j(x) \;=\; \frac{(x/m_j)^{\lambda_j}}{1 + (x/m_j)^{\lambda_j}}, \qquad m_j > 0,\ \lambda_j > 0,\ x \ge 0,\ j = 1, 2 .$$

**Definition (zero interaction potency reference).** Fix a dose pair $(x_1, x_2)$. Adding drug $2$ at dose $x_2$ to drug $1$ is assumed, under zero interaction, to raise the baseline of drug $1$ to $y_2(x_2)$ while leaving its potency $m_1$ and shape $\lambda_1$ unchanged, giving the drug-1-centric prediction

$$y^{1 \leftarrow 2}_{\mathrm{ZIP}} \;=\; y_2(x_2) + \bigl(1 - y_2(x_2)\bigr) y_1(x_1),$$

and symmetrically $y^{2 \leftarrow 1}_{\mathrm{ZIP}} = y_1(x_1) + \bigl(1 - y_1(x_1)\bigr) y_2(x_2)$.

**Theorem.** The two predictions agree, so the reference does not depend on the order in which the agents are added, and with $A = (x_1/m_1)^{\lambda_1}$, $B = (x_2/m_2)^{\lambda_2}$,

$$y_{\mathrm{ZIP}} \;=\; \frac{1 + A + B}{1 + A + B + AB} \cdot \frac{AB + A + B}{1 + A + B} \;=\; \frac{A + B + AB}{(1+A)(1+B)} \;=\; y_1(x_1) + y_2(x_2) - y_1(x_1) y_2(x_2) .$$

That is, the zero interaction potency reference coincides with Bliss independence applied to the two fitted Hill curves.

## Depends on

- [Loewe additivity and the combination index](loewe-additivity-and-the-combination-index.md)
- [Baseline-plus-increment Hill response](../pharmacodynamic-response-models/response.md)

## Proof sketch

Write $y_1(x_1) = A/(1+A)$ and $y_2(x_2) = B/(1+B)$. Then

$$y^{1 \leftarrow 2}_{\mathrm{ZIP}} = \frac{B}{1+B} + \frac{1}{1+B}\cdot\frac{A}{1+A} = \frac{B(1+A) + A}{(1+A)(1+B)} = \frac{A + B + AB}{(1+A)(1+B)},$$

which is symmetric in $A$ and $B$, hence equal to $y^{2 \leftarrow 1}_{\mathrm{ZIP}}$. Expanding the Bliss expression gives $\frac{A}{1+A} + \frac{B}{1+B} - \frac{AB}{(1+A)(1+B)} = \frac{A(1+B) + B(1+A) - AB}{(1+A)(1+B)} = \frac{A + B + AB}{(1+A)(1+B)}$, the same quantity. The model therefore sits between the two classical references: it is derived from a potency argument in the manner of dose addition, yet evaluates to probabilistic independence, and unlike the dose-addition reference it is defined for every dose pair, including combinations whose effect exceeds the maximum attainable by either single agent.

## Sources

- B. Yadav, K. Wennerberg, T. Aittokallio and J. Tang, "Searching for drug synergy in complex dose–response landscapes using an interaction potency model", Computational and Structural Biotechnology Journal 13 (2015), 504–513, Section 2.2, Eqs. (12)–(16) and Appendix A1, <https://doi.org/10.1016/j.csbj.2015.09.001>, PMCID: PMC4759128.
- C. I. Bliss, "The toxicity of poisons applied jointly", Annals of Applied Biology 26 (1939), 585–615.
