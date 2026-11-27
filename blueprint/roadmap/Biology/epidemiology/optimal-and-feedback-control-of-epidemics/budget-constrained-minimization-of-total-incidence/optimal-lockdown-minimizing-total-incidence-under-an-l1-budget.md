# Optimal lockdown minimizing total SIR incidence under an $L^1$ budget

Consider the SIR model with a time-dependent intervention $u(t) \in [0,1]$ that reduces the rate of infectious contacts,

$$
S' = -\beta (1 - u) S I, \qquad I' = \beta (1 - u) S I - \gamma I, \qquad \beta, \gamma > 0,
$$

with $S(0), I(0) > 0$ and $S(0) + I(0) \le 1$. The **total incidence** is $S(0) - S_u(\infty)$, the fraction ever infected after time $0$. Interventions are piecewise continuous and have a linear cost budget $\|u\|_1 = \int_0^\infty u(t)\, dt \le c_1$ and a maximal level $\|u\|_\infty \le c_{\max}$.

**Theorem (optimal intervention).** For any initial state with $S(0), I(0) > 0$, total incidence over all admissible interventions is minimized by a **wait–suppress–relax** intervention

$$
u(t) = \begin{cases} 0, & t \in (0, t_1], \\ c_{\max}, & t \in (t_1, t_2], \\ 0, & t > t_2, \end{cases}
$$

with level $c_{\max}$, duration $t_2 - t_1 = c_1 / c_{\max}$, and a uniquely determined start time $t_1$.

**Theorem (bounds).** For any intervention with finite cost $\|u\|_1 < \infty$, the total incidence, as a fraction of the initial susceptibles, lies between $1 - \gamma/(\beta S(0))$ and $1 - S_0(\infty)/S(0)$, where $S_0(\infty)$ is the final susceptible fraction without intervention.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)
- [Final size of the Kermack–McKendrick epidemic](../../kermack-mckendrick-sir-model/final-size.md)

## Expansion

For finite budget, herd immunity $S < \gamma/\beta$ is reached in finite time, $t_H(u) \le \|u\|_1 + \frac{\log((\beta/\gamma) S(0))}{\beta I(0)} e^{\gamma\|u\|_1}$, and the tails $\int_T^\infty I_u$ decay exponentially and uniformly over the budget class. This lets the infinite-horizon problem be truncated to a finite horizon. On that horizon, any control can be quantized into a bang-bang control with the same $L^1$ norm whose trajectories differ by $O(\beta b h e^{(\beta+\gamma)t})$. Among bang-bang controls, merging scattered suppression intervals into one contiguous block at maximal level, and moving it to the right time, never increases the final size. A monotonicity lemma (adding suppression after the original control ends raises $S(\infty)$) and the inverse of $x \mapsto x - \rho^{-1}\log x$ make this exchange argument precise.

## Sources

- Tom Britton, Lasse Leskelä, "Optimal Intervention Strategies for Minimizing Total Incidence During an Epidemic", SIAM Journal on Applied Mathematics 83 (2023), 354–373, <https://doi.org/10.1137/22m1504433>. Published version of arXiv:2202.07780, cited next; locators there refer to the arXiv version.
- Tom Britton, Lasse Leskelä, "Optimal intervention strategies for minimizing total incidence during an epidemic", arXiv (2022). Theorem 1, Theorem 2, Proposition 3, Proposition 4, Lemma 5, Proposition 6, Lemma 7, Lemma 8. <https://doi.org/10.48550/arXiv.2202.07780>
