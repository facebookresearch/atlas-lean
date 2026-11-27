# Loewe additivity and the combination index

Let two drugs act on a common effect scale $y \in [0, 1]$ (for instance fractional growth inhibition), and assume each drug alone has a strictly increasing dose–effect curve on the range considered, so that for an attainable effect $y$ the dose $X^{(j)}(y)$ of drug $j$ alone producing $y$ is well defined, $j = 1, 2$.

**Definition (Loewe additivity).** For a dose pair $(x_1, x_2)$ the Loewe reference effect $y_{\mathrm{LOEWE}}$ is the solution of

$$\frac{x_1}{X^{(1)}(y_{\mathrm{LOEWE}})} + \frac{x_2}{X^{(2)}(y_{\mathrm{LOEWE}})} \;=\; 1 .$$

In the plane of doses this is the straight isobole joining $X^{(1)}(y)$ and $X^{(2)}(y)$.

**Definition and theorem (combination index).** For an observed combination effect $y_c$ put

$$\mathrm{CI} \;=\; \frac{x_1}{X^{(1)}(y_c)} + \frac{x_2}{X^{(2)}(y_c)} .$$

Then $\mathrm{CI} = 1$ iff $y_c = y_{\mathrm{LOEWE}}$, $\mathrm{CI} < 1$ iff $y_c > y_{\mathrm{LOEWE}}$ (Loewe synergy) and $\mathrm{CI} > 1$ iff $y_c < y_{\mathrm{LOEWE}}$ (Loewe antagonism).

**Parametric form.** With the four-parameter log-logistic (Hill) curves $y = E^{(j)}_{\min} + (E^{(j)}_{\max} - E^{(j)}_{\min}) \dfrac{(x/m_j)^{\lambda_j}}{1 + (x/m_j)^{\lambda_j}}$ one has $X^{(j)}(y) = m_j \left( \dfrac{y - E^{(j)}_{\min}}{E^{(j)}_{\max} - y} \right)^{1/\lambda_j}$, so $y_{\mathrm{LOEWE}}$ solves

$$\frac{x_1}{m_1}\left(\frac{y - E^{(1)}_{\min}}{E^{(1)}_{\max} - y}\right)^{-1/\lambda_1} + \frac{x_2}{m_2}\left(\frac{y - E^{(2)}_{\min}}{E^{(2)}_{\max} - y}\right)^{-1/\lambda_2} = 1,$$

and $y_{\mathrm{LOEWE}} < \min\bigl(E^{(1)}_{\max}, E^{(2)}_{\max}\bigr)$: the reference is undefined whenever the combination exceeds the maximal effect attainable by one of the single agents.

**Sham combination.** If the two agents are the same drug, $m_1 = m_2 = m$, $\lambda_1 = \lambda_2 = \lambda$, $E^{(1)}_{\min} = E^{(2)}_{\min} = E_{\min}$, $E^{(1)}_{\max} = E^{(2)}_{\max} = E_{\max}$, then

$$y_{\mathrm{LOEWE}} \;=\; E_{\min} + (E_{\max} - E_{\min})\,\frac{\bigl((x_1 + x_2)/m\bigr)^{\lambda}}{1 + \bigl((x_1 + x_2)/m\bigr)^{\lambda}},$$

the single-agent response at the pooled dose $x_1 + x_2$.

## Depends on

- [Baseline-plus-increment Hill response](../pharmacodynamic-response-models/response.md)
- [Concentration giving a prescribed response](../pharmacodynamic-response-models/inverse-concentration.md)
- [Interaction references are not interchangeable](../pharmacodynamic-response-models/interact-references-disagree.md)

## Remarks

The equivalence of the three combination-index cases follows from monotonicity of each single-agent curve: $y \mapsto X^{(j)}(y)$ is increasing, so $y_c > y_{\mathrm{LOEWE}}$ gives $X^{(j)}(y_c) > X^{(j)}(y_{\mathrm{LOEWE}})$ for both $j$ and hence a sum strictly below $1$; the two other cases are identical with the inequalities reversed. The upper bound on $y_{\mathrm{LOEWE}}$ holds because $X^{(j)}(y) \to \infty$ as $y \uparrow E^{(j)}_{\max}$ and is undefined above it, so the defining equation has no solution there; this is the structural limitation that motivates references not built on dose equivalence. The sham identity is obtained by substituting the common curve into the defining equation, where the two terms combine into $\bigl((x_1 + x_2)/m\bigr)\bigl((y - E_{\min})/(E_{\max} - y)\bigr)^{-1/\lambda} = 1$ and the displayed Hill form is the unique solution. Dose addition is thus self-consistent for a drug combined with itself, the classical argument in its favour.

## Sources

- B. Yadav, K. Wennerberg, T. Aittokallio and J. Tang, "Searching for drug synergy in complex dose–response landscapes using an interaction potency model", Computational and Structural Biotechnology Journal 13 (2015), 504–513, Section 2.1, Eqs. (2)–(11) and Fig. 1, <https://doi.org/10.1016/j.csbj.2015.09.001>, PMCID: PMC4759128.
- S. Loewe, "The problem of synergism and antagonism of combined drugs", Arzneimittelforschung 3 (1953), 285–290.
