# Existence of forcing-period solutions of the seasonally forced SIR model

Let $S, I, R$ be the susceptible, infective and recovered fractions of a population with birth and death rate $\mu > 0$ and recovery rate $\gamma > 0$, and let the contact rate $\beta(t)$ be a positive continuous $T$-periodic function:

$$

S' = \mu(1-S) - \beta(t)SI, \qquad I' = \beta(t)SI - (\gamma+\mu)I, \qquad R' = \gamma I - \mu R .

$$

Define the basic reproductive number with the time-averaged contact rate,

$$

\mathcal R_0 = \frac{\bar\beta}{\gamma+\mu}, \qquad \bar\beta = \frac1T\int_0^T \beta(t)\,dt .

$$

**Theorem.** If $\mathcal R_0 > 1$, the system has at least one $T$-periodic solution $(S(t),I(t),R(t))$ all of whose components are positive.

When $\mathcal R_0 \le 1$ every solution converges to the disease-free state $(1,0,0)$, so the condition is sharp. The $T$-periodic solution exists even in parameter ranges where typical trajectories are subharmonic (period a multiple of $T$) or chaotic, where it is then unstable; it can be computed by a Galerkin scheme rather than by forward simulation.

## Expansion

Since $S + I + R = 1$ is invariant, it suffices to find a $T$-periodic solution of the planar $(S,I)$ system. The proof uses Leray–Schauder degree. One embeds the problem in a homotopy to an autonomous system (constant contact rate $\bar\beta$), whose endemic equilibrium has nonzero index, and constructs a bounded open set $U$ of positive periodic functions, bounded away from the disease-free state, such that no $T$-periodic solution of any system in the homotopy lies on $\partial U$. A priori bounds come from integrating the equations over a period: for a periodic solution, $\frac1T\int_0^T \beta(t)S(t)\,dt = \gamma + \mu$, and $\mathcal R_0 > 1$ prevents the infective component from tending to zero along the homotopy. Invariance of degree then gives a solution of the forced system in $U$.

## Sources

- Guy Katriel, "Existence of periodic solutions for the periodically forced SIR model", arXiv (2013); Journal of Mathematical Sciences (2014). Section 1 (model and Theorem 1), Section 2 (proof), Section 3 (Galerkin computation). <https://doi.org/10.48550/arXiv.1307.5050>. Published version: Journal of Mathematical Sciences 201(3) (2014), 335–342, <https://doi.org/10.1007/s10958-014-1993-x>; locators above refer to the arXiv version.
