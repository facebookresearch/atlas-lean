# Time-average invasion reproduction number for hierarchical invaders

**Setting.** Let $F(t)$ and $V(t)$ be the $\omega$-periodic $m \times m$ matrices of new infections and of transitions/removals among the $m$ invading compartments of a periodic multi-infection model, linearized at an $A$-endemic periodic solution, as in the definition of the periodic invasion reproduction number $\tilde{\mathcal R}_0^{A}$. Write $\bar M = \frac{1}{\omega}\int_0^\omega M(t)\, dt$ for the period average and define the *time-average* invasion reproduction number

$$\tilde{\mathcal R}_T^{A} = \rho\bigl(\bar F\, \bar V^{-1}\bigr),$$

obtained by replacing every periodic coefficient by its average and applying the autonomous next-generation method.

**Theorem.** If $F(t)$ and $V(t)$ are triangular of the same form for all $t$ (both upper triangular or both lower triangular), then

$$\tilde{\mathcal R}_T^{A} = \tilde{\mathcal R}_0^{A} = \max_{1 \le i \le m} \frac{\bar f_{ii}}{\bar v_{ii}} .$$

In particular the two methods always agree when there is a single invading compartment ($m = 1$): then $\tilde{\mathcal R}_0^{A} = \bar f / \bar v$.

Triangularity of the same form encodes a hierarchy among the invading classes: for lower triangular matrices, invading class $j$ is fed only by classes $i \le j$. Only the invading classes need this structure; the resident infections are unrestricted. Without it the two numbers can differ, so the averaged value can overstate or understate the invaders' ability to establish.

## Depends on

- [Invasion reproduction number of a periodic epidemic model](invasion-reproduction-number-of-a-periodic-epidemic-model.md)

## Expansion

For triangular $F$ and $V$ of the same form, the matrix $-V(t) + F(t)/\lambda$ is triangular, so its principal fundamental matrix over one period is triangular with diagonal entries $\exp\bigl(\omega(\bar f_{ii}/\lambda - \bar v_{ii})\bigr)$. These diagonal entries are the eigenvalues of the monodromy matrix, so

$$\rho\bigl(W(\omega, 0, \lambda)\bigr) = \max_i \exp\Bigl(\omega\bigl(\bar f_{ii}/\lambda - \bar v_{ii}\bigr)\Bigr),$$

which equals $1$ exactly at $\lambda = \max_i \bar f_{ii}/\bar v_{ii}$. On the other side, $\bar V^{-1}$ is triangular of the same form with diagonal $1/\bar v_{ii}$, so $\bar F \bar V^{-1}$ is triangular with diagonal $\bar f_{ii}/\bar v_{ii}$ and the same spectral radius. The condition is weaker than the corresponding condition for basic reproduction numbers, which needs the hierarchy across all infected classes. For example, two pathogens that can superinfect each other (each replacing the other) have no hierarchy among all infected classes, yet each invasion number involves only one invading class and therefore has a closed form. In an application to seasonal influenza and a bacterial respiratory infection, the bacterial invasion number into the influenza-endemic periodic state was obtained this way and used to show how seasonal influenza peaks support year-round bacterial persistence.

## Sources

- C. Mitchell, C. Kribs, "Invasion reproductive numbers for periodic epidemic models", *Infectious Disease Modelling* 4 (2019) 124–141, Theorem 1 and Sections 3.2–3.3 and 4. <https://doi.org/10.1016/j.idm.2019.04.002> (PMC6531838).
- C. Mitchell, C. Kribs, "A comparison of methods for calculating the basic reproductive number for periodic epidemic systems", *Bulletin of Mathematical Biology* 79(8) (2017) 1846–1869. <https://doi.org/10.1007/s11538-017-0309-y>.
