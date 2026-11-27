# Expected resistant subpopulations in a binary-division mutation branching process

**Model.** A tumor starts from one drug-sensitive cell (type $0$) at generation $0$. In each generation every cell divides into two daughters. A type-$0$ cell produces, with probability $\alpha_{(0,q)}$, exactly one daughter of resistant type $q \in \{1, \dots, m\}$ (and one type-$0$ daughter); with probability $\alpha_{(0,0)} = 1 - \sum_{q \ge 1} \alpha_{(0,q)}$ both daughters are type $0$. Resistant cells never revert and divide into two daughters of their own type. Writing $\pi(t)$ for the vector of type counts at generation $t$,

$$\pi(t+1) \sim \mathrm{Mult}\big(\pi_0(t),\ \boldsymbol{\alpha}_{(0)}\big) + 2\pi(t) - \mathbf{e}_0 \circ \pi(t),$$

where $\boldsymbol{\alpha}_{(0)} = (\alpha_{(0,0)}, \dots, \alpha_{(0,m)})$.

**Proposition.** For every $t \in \mathbb{Z}_{\ge 0}$,

$$\mathbb{E}\,\pi_0(t) = (1 + \alpha_{(0,0)})^t, \qquad \mathbb{E}\,\pi_q(t+1) = \sum_{k=0}^{t} 2^k\, \alpha_{(0,q)}\, (1 + \alpha_{(0,0)})^{t-k} \quad (q \ge 1).$$

## Expansion

A type-$0$ cell has on average $2\alpha_{(0,0)} + (1 - \alpha_{(0,0)}) = 1 + \alpha_{(0,0)}$ type-$0$ daughters, so conditioning on generation $t$ gives $\mathbb{E}\,\pi_0(t+1) = (1 + \alpha_{(0,0)})\,\mathbb{E}\,\pi_0(t)$, and induction from $\pi_0(0) = 1$ gives the first formula. Resistant counts double and receive on average $\alpha_{(0,q)}\,\mathbb{E}\,\pi_0(t)$ new mutants, so $\mathbb{E}\,\pi_q(t+1) = 2\,\mathbb{E}\,\pi_q(t) + \alpha_{(0,q)}(1 + \alpha_{(0,0)})^t$ with $\pi_q(0) = 0$; unrolling this linear recursion yields the stated sum. Because $2 > 1 + \alpha_{(0,0)}$, the resistant expectation eventually grows like $2^{t}$ times a constant, so small mutation probabilities still create resistant clones that dominate the tail of the scenario distribution used to plan neoadjuvant therapy.

## Sources

- Temitayo Ajayi, Seyedmohammadhossein Hosseinian, Andrew J. Schaefer, Clifton D. Fuller, "Combination Chemotherapy Optimization with Discrete Dosing", INFORMS Journal on Computing 36 (2024), 434–455, <https://doi.org/10.1287/ijoc.2022.0207>. Published version of arXiv:2111.02000, cited next; locators there refer to the arXiv version.
- Temitayo Ajayi, Seyedmohammadhossein Hosseinian, Andrew J. Schaefer, Clifton D. Fuller, "Combination Chemotherapy Optimization with Discrete Dosing", arXiv (2021). Appendix "Estimating Initial Tumor Population via a Branching Process" (proposition on expected cell-type populations). <https://doi.org/10.48550/arXiv.2111.02000>
