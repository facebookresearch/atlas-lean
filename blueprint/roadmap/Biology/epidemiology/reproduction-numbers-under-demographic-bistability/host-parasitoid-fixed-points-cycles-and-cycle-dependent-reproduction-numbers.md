# Host-parasitoid fixed points, cycles and cycle-dependent reproduction numbers

**Model.** In discrete generations, host eggs $E$ and parasitoid larvae $L$ follow a Beddington-type Nicholson-Bailey model in which hosts first survive Ricker competition and are then parasitized:

$$E(t+1) = \lambda E(t)\,e^{-\mu E(t)}e^{-aL(t)}, \qquad L(t+1) = b\lambda E(t)\,e^{-\mu E(t)}\bigl(1 - e^{-aL(t)}\bigr),$$

with host fecundity $\lambda$, competition $\mu$, searching efficiency $a$ and parasitoid yield $b$.

**Theorem (demography).**
- The model has a strictly positive host-parasitoid coexistence fixed point if $\lambda > e^{\mu/(ab)}$.
- It has a nontrivial host-only 2-cycle iff $\lambda > e^2$ (the period-doubling of the Ricker map $E \mapsto \lambda Ee^{-\mu E}$).

So for large fecundity the host-parasitoid demography is multistable: populations may sit at a fixed point or oscillate on a cycle for the same parameters.

**Reproduction numbers.** Adding a pathogen spread through the host-parasitoid interaction, the endemic fixed point exists and is unique iff $\mathcal{R}_{0_1} > 1$, where $\mathcal{R}_{0_1}$ is the reproduction number computed at the demographic fixed point. A second number $\mathcal{R}_{0_2}$, computed along the demographic 2-cycle, can exceed one while $\mathcal{R}_{0_1} < 1$: the same parameters then predict eradication when populations rest at the fixed point and persistence when they oscillate. The analogous tick-host model (larvae, nymphs and adults feeding on several host species) has a unique endemic fixed point iff its demographic coexistence point is stable ($\mathcal{R}_d > 1$) and $\mathcal{R}_{0_1} > 1$.

## Expansion

A reproduction number linearizes the infection subsystem about a disease-free demographic state. When that state is a fixed point, the next-generation operator is a constant matrix; on a $k$-cycle one must instead account for growth over a whole period, for instance through the product of the $k$ linearized maps. Because infection rates depend on densities that are higher in one phase of the cycle, the cycle average can exceed the fixed-point value, which is why demographic bistability turns into epidemiological bistability. Control assessments must therefore specify which demographic attractor the system occupies.

## Sources

- C. Peterson, E. Gallo, C. Kribs, "Basic Reproductive Numbers in Host-Parasite Systems with Demographic Bistability" (2026), tick-host model (fullsystem) and Theorem 1, host-parasitoid model (system2noinfect), Theorems 2-4, <https://doi.org/10.48550/arXiv.2611.04990>.
