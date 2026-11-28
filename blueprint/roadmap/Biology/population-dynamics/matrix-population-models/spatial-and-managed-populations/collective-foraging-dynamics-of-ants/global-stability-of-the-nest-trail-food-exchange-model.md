# Global stability of the nest–trail food-exchange model

**Model.** A foraging colony of arboreal turtle ants is split into a trail group of $M$ ants (foragers $F$ and suppliers $S$, as fractions with $F+S=1$) and a nest group of $N$ ants (interior ants $I$ and receivers $R$, $I+R=1$). Foragers return to supply food at rate $\gamma>0$ and interior ants become receivers at rate $\alpha>0$; a supplier and a receiver must meet to hand off food, which returns both to their other compartments at mass-action rates. The dynamics reduce to

$$\dot R = \alpha(1-R) - \beta\frac{M}{N}RS, \qquad \dot S = \gamma(1-S) - \beta\frac{N}{M}RS,$$

with interaction parameter $\beta>0$.

**Theorem.** The square $[0,1]^2$ is positively invariant, and the system has a unique equilibrium $(R^{*},S^{*})$ in it,

$$S^{*} = \frac{A-B-1+\sqrt{(A-B-1)^2+4AB}}{2A}, \qquad R^{*} = \frac{B(1-S^{*})}{S^{*}}, \qquad A = \frac{\gamma M^2}{\alpha N^2},\quad B = \frac{\gamma M}{\beta N},$$

which is globally attracting on $[0,1]^2$. Hence the constant-rate food exchange cannot oscillate: periodic flow of ants in and out of the nest requires additional feedback, such as a trail pheromone that is laid by returning foragers and modulates the forager return rate $\gamma$, which turns the model into a four-dimensional system with mixed positive and negative feedback.

## Expansion

The planar system is competitive: increasing $R$ decreases $\dot S$ and increasing $S$ decreases $\dot R$. Planar competitive flows have no periodic orbits, so bounded trajectories converge to equilibria; eliminating $R$ from the nullclines gives a quadratic in $S$ with exactly one root in $(0,1]$, and the unique equilibrium is therefore globally attracting.

## Sources

- A. Valentine, D. M. Gordon, A. Bizyaeva, "Mixed-feedback oscillations in the foraging dynamics of arboreal turtle ants", *2025 IEEE 64th Conference on Decision and Control (CDC)* (2025), 3806–3811, Section 2 (model) and Theorems 3.1, 4.1–4.2, <https://doi.org/10.1109/cdc57313.2025.11312995> (preprint arXiv:2504.11551).
