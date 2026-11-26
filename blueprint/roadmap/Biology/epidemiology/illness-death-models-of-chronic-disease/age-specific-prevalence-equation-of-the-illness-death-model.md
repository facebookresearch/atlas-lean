# Age-specific prevalence equation of the illness–death model

**Model.** For an irreversible chronic disease, individuals move from *Normal* to *Disease* with age-specific incidence rate $i(a)$, and die with mortality $m_0(a)$ if healthy and $m_1(a)$ if diseased. Assume the rates do not depend on calendar time, $m_1$ does not depend on disease duration, the population is closed, and birth rates are constant in time. The numbers of healthy and diseased persons of age $a$ satisfy

$$
\frac{dS}{da}=-\big(i(a)+m_0(a)\big)S,\qquad \frac{dC}{da}=i(a)S-m_1(a)C.
$$

**Theorem.** Let $m_0,m_1,i\in C^0([0,\infty))$ and $S,C\in C^1([0,\infty))$ solve this system with $S(a)+C(a)>0$. Then the age-specific prevalence $p=C/(S+C)$ is differentiable and

$$
\frac{dp}{da}=(1-p)\Big(i-p\,(m_1-m_0)\Big).
$$

Consequently, the incidence can be recovered from prevalence and mortality data,

$$
i(a)=\frac{p'(a)}{1-p(a)}+p(a)\big(m_1(a)-m_0(a)\big),
$$

and if the relative mortality $R=m_1/m_0$ and the general mortality $m=pm_1+(1-p)m_0$ are known, $m_1-m_0=m(R-1)/(1+p(R-1))$.

## Expansion

Differentiate $p=C/(S+C)$ using the quotient rule and substitute the two ODEs; the terms reorganize into the inflow $i(1-p)$ minus the selective loss $p(1-p)(m_1-m_0)$ caused by excess mortality of the diseased. The equation is a Riccati-type ODE that links three epidemiological quantities without needing the population sizes. Its practical value is the inverse problem: a single cross-sectional prevalence survey plus mortality estimates yields age-specific incidence, which is otherwise only measurable through long follow-up studies; the source applies it to dementia in Germany.

## Sources

- Ralph Brinks, "A new method for deriving incidence rates from prevalence data and its application to dementia in Germany", arXiv:1112.2720: Section "The new relation between incidence, prevalence and mortality": the compartment ODEs, assumptions 1–4 and the central theorem on the prevalence derivative; Section "Application to dementia". <https://doi.org/10.48550/arXiv.1112.2720>
