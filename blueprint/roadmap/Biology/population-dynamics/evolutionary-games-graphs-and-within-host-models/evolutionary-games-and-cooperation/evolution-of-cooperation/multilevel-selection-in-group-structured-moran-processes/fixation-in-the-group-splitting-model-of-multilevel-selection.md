# Fixation in the group-splitting model of multilevel selection

**Model.** A population is divided into $m \ge 2$ groups of at most $n$ individuals of types $A$ and $B$, which play the game $\begin{pmatrix} a & b\\ c & d\end{pmatrix}$ within their group. In each step an individual is chosen from the whole population with probability proportional to fitness and its offspring joins the same group. If the group then exceeds $n$ members, with probability $q$ it splits into two and a uniformly chosen group is removed; with probability $1 - q$ a uniformly chosen member of that group is removed instead.

**Two-level decomposition.** In the limit $q \to 0$, groups are almost always full and homogeneous between splits, and fixation of a single mutant $A$ factorizes as

$$\rho_A = \phi_A \cdot \Phi_A,$$

where $\phi_A$ is the fixation probability of one $A$ in a group of $n$ playing the frequency-dependent Moran process, and $\Phi_A$ is the fixation probability of one all-$A$ group among $m - 1$ all-$B$ groups. Between pure groups the process is a frequency-independent Moran process with

$$\frac{P^-(l)}{P^+(l)} = \frac{f_B(0)}{f_A(n)},$$

where $l$ is the number of all-$A$ groups, $f_A(n)$ the fitness in an all-$A$ group and $f_B(0)$ in an all-$B$ group.

**Theorem (exponential fitness, any intensity).** With $f = e^{\beta\pi}$ (so $\pi_A(n) = a$, $\pi_B(0) = d$),

$$\Phi_A = \frac{1 - e^{-\beta(a - d)}}{1 - e^{-\beta(a - d)m}}, \qquad \Phi_B = \frac{1 - e^{\beta(a - d)}}{1 - e^{\beta(a - d)m}} \quad (\beta(a - d) \ne 0),$$

and, for every $\beta \ge 0$,

$$\frac{\rho_B}{\rho_A} = \exp\left[-\beta\left(\frac n2(a + b - c - d) + (m - 2)(a - d)\right)\right].$$

Hence, for $\beta > 0$, $\rho_A > \rho_B$ if and only if

$$n(a + b - c - d) + 2(m - 2)(a - d) > 0 .$$

The same condition holds to first order under weak selection with linear fitness $1 - w + w\pi$, where

$$\rho_A \approx \frac{1}{nm} + \frac{w}{6nm}\bigl[-2a - b - c + 4d + n(a + 2b - c - 2d) + 3(m - 1)(a - d)\bigr].$$

For a prisoner's dilemma with benefit $b_0$ and cost $c_0$ of cooperation, the condition reads $b_0/c_0 > 1 + n/(m - 2)$ for $m \ge 3$ and never holds for $m = 2$.

**Interpretation.** Many small groups ($m \gg n$) favour the Pareto-efficient equilibrium ($A$ wins if $a > d$); few large groups ($m \ll n$) reduce to risk dominance within a single well-mixed population ($a + b > c + d$). Under strong selection both $\rho_A$ and $\rho_B$ become small, since cooperators rarely fix within a group and defector groups rarely take over, but their ratio remains meaningful.

## Depends on

- [Exponential payoff-to-fitness Moran process: exact fixation probabilities](exponential-payoff-to-fitness-moran-process-exact-fixation-probabilities.md)
- [Fixation probability in a frequency-dependent Moran process](../../../../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)

## Proof depends on

- [Moran fixation probability](../../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Expansion

At the group level the ratio $P^-/P^+ = e^{\beta(d - a)}$ is constant, so $\Phi_A$ is the constant-fitness Moran fixation probability with relative fitness $e^{\beta(a - d)}$ in a population of $m$ groups, and $\Phi_B/\Phi_A = e^{-\beta(a - d)(m - 1)}$. Multiplying by the within-group ratio $\phi_B/\phi_A = \exp[-\beta(\frac n2(a + b - c - d) - a + d)]$ gives exponent $-\beta[\frac n2(a + b - c - d) - (a - d) + (m - 1)(a - d)]$, which is the stated one. The factorization is exact only for $q \to 0$; simulations show that larger $q$ favours cooperators, because groups stay smaller and mixed groups can split.

## Sources

- A. Traulsen, N. Shoresh, M. A. Nowak, *Analytical results for individual and group selection of any intensity*, Bulletin of Mathematical Biology 70 (2008), <https://doi.org/10.1007/s11538-008-9305-6>, PMCID PMC2574888. Section 4 (group-splitting model, $\rho_A = \phi_A\Phi_A$, Eq. (30), weak-selection Eqs. (31)–(32), condition Eq. (33) and the benefit-to-cost threshold $1 + n/(m-2)$), Section 5 ($\Phi_A$, $\Phi_B$ and the ratio $\rho_B/\rho_A$, Eq. (40), valid for any intensity of selection), Appendix A.
- A. Traulsen, M. A. Nowak, *Evolution of cooperation by multilevel selection*, Proc. Natl. Acad. Sci. USA 103 (2006), 10952–10955, <https://doi.org/10.1073/pnas.0602530103>.
