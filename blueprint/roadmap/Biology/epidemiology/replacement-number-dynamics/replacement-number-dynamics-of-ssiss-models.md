# Replacement number dynamics of two-susceptible-class SIR-type models

**SSISS model.** Split a normalized population $S_1 + S_2 + I = 1$ into highly susceptible $S_1$, less susceptible $S_2$ and infectious $I$, with standard incidence, transmission coefficients $\beta_1 > \beta_2$ (negative values are allowed to absorb compartment-dependent birth and death rates), recovery rates $\gamma_1,\gamma_2 \ge 0$ from $I$ into $S_1, S_2$ with $\gamma_1 + \gamma_2 = 1$ (time measured in units of the mean infectious period), and smooth flows $\Omega_1,\Omega_2$ between the susceptible classes (vaccination, waning, behaviour):

$$
\begin{pmatrix}\dot S_1\\ \dot S_2\end{pmatrix}
= \left[-I\begin{pmatrix}\beta_1 & 0\\ 0 & \beta_2\end{pmatrix} + \begin{pmatrix}-\Omega_1 & \Omega_2\\ \Omega_1 & -\Omega_2\end{pmatrix}\right]\begin{pmatrix}S_1\\ S_2\end{pmatrix} + I\begin{pmatrix}\gamma_1\\ \gamma_2\end{pmatrix}.
$$

The model is *admissible* if $\gamma_i \ge 0$ and $\Omega_j|_{S_i = 0} \ge 0$ for $j \ne i$, which keeps the physical triangle $\{S_1,S_2,I \ge 0\}$ forward invariant.

**Replacement number picture.** Let $X := \beta_1 S_1 + \beta_2 S_2$ be the replacement number. Then $I = 1 - S_1 - S_2$ satisfies $\dot I = (X - 1)I$, and the linear change of variables $(S_1,S_2) \mapsto (X,I)$ turns the system into a *replacement number dynamics* (RND)

$$
\dot X = f(X,I), \qquad \dot I = (X-1)I
$$

for a smooth $f$. Explicitly, writing the model in a canonical gauge one has

$$
f(X,I) = \lambda I + (1-I)P(X,I) + X\,Q(X,I), \qquad \lambda = \beta_1\gamma_1 + \beta_2\gamma_2,
$$

with $P, Q$ determined by $(\beta_i,\Omega_i)$. Conversely, for every smooth $f$ and every choice $\beta_1 > \beta_2$ there is a unique SSISS model (up to the redundancy $\Omega \mapsto \Omega + K\cdot(S_2,S_1)$, which does not change the vector field) whose RND is $f$. Fixing $f$ and varying $(\beta_1,\beta_2)$ gives a family of isomorphic SSISS systems on which the group $G_\sigma = \{g \in \mathrm{GL}_2(\mathbb{R}) : \det g > 0,\ \sigma g = \sigma\}$, $\sigma = (1,1)$, acts freely and transitively.

**Consequence.** Equilibria of any SSISS model are the zeros of $f(\cdot,0)$ (disease-free) and of $f(1,\cdot)$ (endemic, where $X = 1$), so existence and stability questions reduce to one-variable root problems.

## Depends on

- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Because the incidence is linear in $S_1,S_2$, $\dot I = (\beta_1 S_1 + \beta_2 S_2 - 1)I$ already depends on $(S_1,S_2)$ only through $X$. The map $(S_1,S_2) \mapsto (X, 1 - S_1 - S_2)$ is linear and invertible since $\beta_1 \ne \beta_2$, so $\dot X = \beta_1\dot S_1 + \beta_2 \dot S_2$ is some smooth function of $(X,I)$. Writing $\dot X = \langle\beta, M(S)S\rangle + I\langle\beta,\gamma\rangle$ and decomposing $M$ along the dual basis gives the $\lambda I + (1-I)P + XQ$ form; the splitting $Q = X^{-1}(f(X,I) - f(0,I))$, $P = (1-I)^{-1}(f(0,I) - f(0,1)I)$, $\lambda = f(0,1)$ inverts it. Two choices of $\beta$ give SSISS systems related by a linear map fixing $S_1 + S_2$, which is the $G_\sigma$-action.

## Sources

- F. Nill, The replacement number dynamics in SIR-type epidemic models I: From SSISS to RND picture, arXiv:2410.19532 (2024), Section 2 (SSISS model) and Section 3, Definition 3.3, Proposition 3.4 and Theorem 3.8, <https://doi.org/10.48550/arXiv.2410.19532>.
