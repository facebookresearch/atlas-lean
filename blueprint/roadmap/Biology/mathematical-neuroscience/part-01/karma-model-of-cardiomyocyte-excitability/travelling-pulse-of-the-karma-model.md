# Travelling pulse of the Karma model

With diffusion coefficient $D = O(1)$ and co-moving coordinate $z = x + ct$, travelling waves of the spatially extended Karma model with $I = 0$ solve

$$E_z = w, \qquad Dw_z = cw + E - 2\left(E^* - n^M\right)\left(E^2 - \delta E^3\right), \qquad c\,n_z = \varepsilon\left(\frac{1}{n_B}\theta(E-1) - n\right),$$

a $(2,1)$ fast–slow system (Gonzalez Herrero, Kuehn and Tsaneva-Atanasova 2021, Eqs. 3.17–3.18), with the rectifier $\theta(x) = \max\{0, x\}$ of the space-clamped model. For fixed $n$ with $n^M \le 1$ (so that the square root below is real) the fast subsystem has equilibria $p_0 = (0,0)$ and $p_{1,2} = \left(2 \mp 2\sqrt{1 - \frac{1}{2(E^* - n^M)}},\, 0\right)$, of which $p_0$ and $p_2$ are saddles and $p_1$ is unstable.

**Lemma (fast fronts).** For every $n \in [0,1]$ there is a speed $c > 0$ with a heteroclinic front of the fast subsystem: from $p_0$ to $p_2$ when $n^M < 15/16$ and from $p_2$ to $p_0$ when $n^M > 15/16$, with a double heteroclinic orbit at $c = 0$ when $n^M = 15/16$. For $n = 1$ there is $c_{\min}$ such that a front from $p_2$ to $p_0$ exists for every $c \ge c_{\min}$ (Lemma 1, established by a numerical shooting computation).

**Theorem.** In the singular limit there is a homoclinic candidate orbit to the rest state, $\lim_{z\to\pm\infty}(E,n) = (0,0)$, built from an excitation front, a slow segment on the excited branch, a recovery back and a slow return (Theorem 8), and it perturbs to a homoclinic orbit, i.e. a travelling action-potential pulse, for small $\varepsilon > 0$ (Theorem 9).

## Depends on

- [Critical manifold and singular orbits of the Karma model](critical-manifold-and-singular-orbits-of-the-karma-model.md)

## Expansion

The value $15/16$ is the Maxwell (equal-area) point of the fast nonlinearity. At $n^M = 15/16$, $E^* - n^M = 9/16$ and the reaction term $g(E) = -E + \tfrac98 E^2 - \tfrac{9}{32}E^3$ has zeros $0$, $4/3$ and $8/3$ (so $p_2 = (8/3, 0)$), and $\int_0^{8/3} g(E)\,dE = 0$; hence a standing front ($c = 0$) joins $p_0$ and $p_2$ in both directions. Moving $n^M$ below or above $15/16$ changes the sign of this integral and therefore the direction in which a front with $c > 0$ travels. The slow flow on the critical manifold is that of the ODE model scaled by $1/c$, so the same equilibria appear. Fenichel theory away from $E = 1$ and the fold point gives persistence.

## Sources

- M. E. Gonzalez Herrero, C. Kuehn and K. Tsaneva-Atanasova, *Reduced models of cardiomyocytes excitability: comparing Karma and FitzHugh–Nagumo*, Bulletin of Mathematical Biology 83 (2021), Eqs. (3.17)–(3.22), Lemma 1 and Theorems 8–9. <https://doi.org/10.1007/s11538-021-00898-0> (PMCID: PMC8253715)
