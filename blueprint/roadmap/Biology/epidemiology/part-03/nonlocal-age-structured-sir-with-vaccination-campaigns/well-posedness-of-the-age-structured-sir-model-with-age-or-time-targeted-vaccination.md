# Well-posedness of the nonlocal age-structured SIR model with age- or time-targeted vaccination

**Model.** Densities $S(t,a)$, $I(t,a)$, $R(t,a)$ of susceptible, infected and removed (recovered or immune) individuals of age $a \ge 0$ at time $t \in \mathbb I = [0,T]$ satisfy the McKendrick-type system with nonlocal age-dependent transmission

$$\partial_t S + \partial_a S = -d_S S - S\int_0^\infty \lambda(a,a')\,I(t,a')\,da', \qquad \partial_t I + \partial_a I = -d_I I + S\int_0^\infty \lambda(a,a')\,I(t,a')\,da' - r_I I, \qquad \partial_t R + \partial_a R = -d_R R + r_I I,$$

with initial age profiles and birth boundary data at $a = 0$. Vaccination enters not as a source term but through jump conditions:

- **age-targeted policy:** at prescribed ages $\bar a_1 < \dots < \bar a_N$ a fraction $\eta_j(t) \in [0,1]$ of susceptibles is vaccinated, $S(t,\bar a_j+) = (1-\eta_j(t))S(t,\bar a_j-)$, $I(t, \bar a_j+) = I(t, \bar a_j-)$, $R(t,\bar a_j+) = R(t,\bar a_j-) + \eta_j(t)S(t,\bar a_j-)$;
- **time-targeted policy:** at campaign times $\bar t_1 < \dots < \bar t_N$ a fraction $\nu_k(a) \in [0,1]$ of susceptibles of each age is vaccinated, $S(\bar t_k+, a) = (1-\nu_k(a))S(\bar t_k-, a)$, $I$ unchanged, and $R$ gains $\nu_k(a) S(\bar t_k-,a)$.

Assume $\lambda$ is continuous, bounded and Lipschitz in the age of the susceptible, the rates $d_S, d_I, d_R, r_I$ are Carathéodory functions that are bounded and Lipschitz in age, and the data are nonnegative and integrable with bounded variation.

**Theorem.** For every choice of vaccination ages (respectively times) and every control of bounded variation $\eta \in \mathrm{BV}(\mathbb I; [0,1]^N)$ (respectively $\nu$), the problem has a unique solution

$$(S, I, R) \in C^{0,1}\big(\mathbb I; L^1(\mathbb R^+; \mathbb R^3)\big), \qquad S, I, R \ge 0,$$

depending Lipschitz continuously on the initial datum in $L^1$ and on the control in $L^\infty$.

The Lipschitz dependence on the vaccination controls is what makes cost functionals of the form "infections plus vaccination cost" continuous on the control set, the basis for optimizing vaccination ages or campaign times.

## Expansion

Both policies are special cases of a general initial–boundary value problem for $n$ coupled transport equations $\partial_t u_i + \partial_x(g_i u_i) = (\alpha_i[u] + \gamma_i)\cdot u$ on $\mathbb R^+$, with nonlocal Lipschitz coupling $\alpha_i$ and boundary/interface conditions given by Lipschitz functions of traces. For that problem, existence and uniqueness of $L^1$ solutions with $\mathrm{BV}$ bounds follow from a fixed point on characteristics with Grönwall-type stability estimates; a positivity corollary holds when the data and boundary maps are nonnegative and the total source is nonpositive. The vaccination jumps are interface conditions at the ages $\bar a_j$, or restarts at the times $\bar t_k$, which conserve $S + I + R$ and preserve nonnegativity because $\eta_j, \nu_k \in [0,1]$.

## Sources

- Rinaldo M. Colombo, Mauro Garavello, "Well Posedness and Control in a NonLocal SIR Model", arXiv (2019). Section 2 (model and vaccination conditions), Theorems 2.1 and 2.2, Theorem 3.1, Corollary 3.3. <https://doi.org/10.48550/arXiv.1910.07389>. Published version: Applied Mathematics & Optimization 84(1) (2021), 737–771, <https://doi.org/10.1007/s00245-020-09660-9>; locators above refer to the arXiv version.
