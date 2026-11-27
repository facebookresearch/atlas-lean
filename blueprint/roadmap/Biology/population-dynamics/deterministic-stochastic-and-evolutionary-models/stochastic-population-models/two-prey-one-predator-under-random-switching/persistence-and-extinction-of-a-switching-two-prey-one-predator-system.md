# Persistence and extinction of a switching two-prey one-predator system

**Model.** Prey $X_1, X_2$ and predator $X_3$ follow

$$
\dot X_i = X_i f_i(\mathbf{X}, \xi(t)), \qquad
f_1 = r - x_1 - b_1 x_2 - c_1(j) x_3, \quad
f_2 = r - x_2 - b_2 x_1 - c_2(j) x_3, \quad
f_3 = e_1(j) x_1 + e_2(j) x_2 - d,
$$

where $\xi(t) \in \{1, 2\}$ is an irreducible continuous-time Markov chain (environmental state) and only the predation coefficients $c_i(j)$ and conversion efficiencies $e_i(j)$ depend on the state. In a fixed environment, competition can rule out coexistence of the two prey without the predator, while the predator can mediate three-species coexistence.

**Results.**
1. *(Well-posedness and dissipativity.)* For every initial state there is a unique solution; there is a compact set that every nonnegative solution eventually enters and never leaves, and interior initial conditions remain interior.
2. *(Boundary invariant measures.)* Under the conditions making each prey–predator pair viable, there are unique invariant probability measures $\mu_{13}$ on $\{x_1, x_3 > 0, x_2 = 0\} \times \{1, 2\}$ and $\mu_{23}$ on $\{x_2, x_3 > 0, x_1 = 0\} \times \{1, 2\}$.
3. *(Persistence.)* Define the invasion rates of the missing prey

$$
\lambda_2(\mu_{13}) = \int \sum_j \bigl(r - b_2 x_1 - c_2(j) x_3\bigr)\, \mu_{13}(dx_1, dx_3, j), \qquad
\lambda_1(\mu_{23}) = \int \sum_j \bigl(r - b_1 x_2 - c_1(j) x_3\bigr)\, \mu_{23}(dx_2, dx_3, j).
$$

If both are positive, the three species persist stochastically: for every $\varepsilon > 0$ there is $\delta > 0$ with $\liminf_{t\to\infty}\mathbb{P}_{\mathbf{x}}\{X_i(t) \ge \delta,\ i = 1,2,3\} \ge 1 - \varepsilon$; under a Hörmander-type bracket condition the system is strongly stochastically persistent.
4. *(Extinction.)* If $\lambda_2(\mu_{13}) < 0$, then for initial conditions with $X_2$ small, with probability close to $1$, $X_2(t) \to 0$ with $\frac{1}{t}\log X_2(t) \to \lambda_2(\mu_{13})$; symmetrically for $\lambda_1(\mu_{23}) < 0$.

## Proof sketch

The invasion rate is the long-run per-capita growth rate of a rare species when the resident community is at its stationary regime: by Itô-type ergodic averaging of $\frac{d}{dt}\log X_i = f_i$, a species that is rare grows like $e^{\lambda t}$. Positivity of both invasion rates gives a Lyapunov function $V = \prod_i x_i^{-p_i}$ (suitably weighted) whose expectation contracts near the boundary, which yields persistence; negativity of one rate gives the matching extinction statement. Switching can save a species from extinction even when the same competitor is dominant in each fixed environment.

## Related topics

- [Lotka–Volterra predator–prey model](../../../lotka-volterra-predator-prey-model/README.md)

## Sources

- Alexandru Hening, Dang H. Nguyen, Nhu Nguyen and Harrison Watts, "Random Switching in an Ecosystem with Two Prey and One Predator", *SIAM Journal on Mathematical Analysis* 55 (2023), 347–366, <https://doi.org/10.1137/21m1459836>. Preprint version: arXiv:2111.12750 (2021), Theorems 1–4, Lemmas 2.1–2.3, Lemma 3.1, Proposition 3.1, <https://doi.org/10.48550/arXiv.2111.12750>.
