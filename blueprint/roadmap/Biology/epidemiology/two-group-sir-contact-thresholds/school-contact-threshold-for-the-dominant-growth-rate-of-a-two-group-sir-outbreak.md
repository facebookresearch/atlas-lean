# School-contact threshold for the dominant growth rate of a two-group SIR outbreak

**Model.** Split a population into a schooling group $1$ and a non-schooling group $2$ with SIR dynamics, transmission rates $\beta_{ij} > 0$ from group $j$ to group $i$, and time measured in units of the infectious period:

$$S_i' = -S_i \sum_{j} \beta_{ij} I_j, \qquad I_i' = S_i \sum_j \beta_{ij} I_j - I_i, \qquad R_i' = I_i \qquad (i = 1,2).$$

Linearizing the infected equations at the start of an outbreak gives $\vec I\,' = (A - \mathrm{Id})\vec I$ with the reproduction matrix

$$A = \begin{pmatrix} a_{11} & a_{12} \\ a_{21} & a_{22} \end{pmatrix} = \begin{pmatrix} \beta_{11} S_1(0) & \beta_{12} S_1(0) \\ \beta_{21} S_2(0) & \beta_{22} S_2(0) \end{pmatrix},$$

whose eigenvalues $\lambda_{\max} > \lambda_{\min}$ are real, and $\vec I(t) = e^{-t}\big(e^{\lambda_{\max} t}\vec W + e^{\lambda_{\min} t}\vec V\big)$ with $\vec W > 0$.

**Theorem.** As a function of the in-school entry $a_{11} \ge 0$, with the other entries fixed and positive,

$$\lambda_{\max}(a_{11}) = \frac{a_{11} + a_{22}}{2} + \sqrt{\Big(\frac{a_{11} - a_{22}}{2}\Big)^2 + a_{12} a_{21}}$$

is increasing and convex, and its slope

$$\lambda_{\max}'(a_{11}) = \frac12 + \frac{a_{11} - a_{22}}{2\sqrt{(a_{11} - a_{22})^2 + 4a_{12}a_{21}}}$$

is a sigmoid in $a_{11}$ rising from near $0$ to near $1$, with its inflection (steepest change) at $a_{11} = a_{22}$. Quantitatively, for every $\alpha \in \big(0, a_{22}/\sqrt{a_{12}a_{21}}\big)$, writing $c = \sqrt{a_{12}a_{21}}$,

$$\frac{\lambda_{\max}'(a_{22} + \alpha c) - \lambda_{\max}'(a_{22} - \alpha c)}{\lambda_{\max}'(a_{22} - \alpha c) - \lambda_{\max}'(0)} \ge \frac{2\alpha}{\sqrt{4 + \alpha^2} - \alpha},$$

and the same lower bound holds with the denominator replaced by $\lambda_{\max}'(2a_{22}) - \lambda_{\max}'(a_{22} + \alpha c)$. Consequently the in-school transmission rate has little influence on the epidemic growth rate below, and a strong influence above, the critical value

$$\beta_{11}^* = \beta_{22}\, \frac{S_2(0)}{S_1(0)};$$

for any $k > 0$, the deviation of the infected curve caused by raising $a_{11}$ from $0$ to just above $a_{22}$ eventually exceeds $k$ times the deviation caused by raising it to just below $a_{22}$.

## Expansion

The formula for $\lambda_{\max}$ is the larger root of $\lambda^2 - (a_{11} + a_{22})\lambda + a_{11}a_{22} - a_{12}a_{21} = 0$. In the variable $u = (a_{11} - a_{22})/c$ its derivative is $\lambda_{\max}' = \tfrac12\big(1 + u/\sqrt{u^2 + 4}\big)$, which is point-symmetric about $u = 0$, so increments of $a_{11}$ around $a_{22}$ change the slope much more than the same increments far below it; the ratio bound is an explicit computation in $u$, and the two ratios coincide by this symmetry. Since the dominant exponential term controls $\vec I(t)$ for large $t$, differences in $\lambda_{\max}$ are amplified over time. The interpretation is a phase transition: school openings barely matter while in-school contacts are kept below the non-school contact level, which can reconcile studies reaching opposite conclusions on slightly different parameter estimates. Analogous thresholds appear under lockdown and vaccination of non-schooling individuals.

## Sources

- A. Gandolfi, A. Aspri, E. Beretta and K. Jamshad, "A new threshold reveals the uncertainty about the effect of school opening on diffusion of Covid-19", arXiv:2104.04136 (2021), Methods ("SIR model with two subclasses", "A phase transition for school opening during an outbreak"): the linearized system, the representation lemma, the eigenvalue theorem and its corollary, with proofs in the appendices, <https://doi.org/10.48550/arXiv.2104.04136>.
