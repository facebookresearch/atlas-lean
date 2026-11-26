# Exposure Potential

Let $U$ be a set of units, $\Omega$ a set of assignments, $e : U \times \Omega \to \Delta$ an exposure mapping and $y^r : U \times \Omega \to \mathbb R$ the randomization potential outcomes. The exposure-specific potential outcome of unit $i$ at exposure $d$ is

$$y_i(d) = \begin{cases} y^r_i(z_{i,d}) & \text{if some } z \in \Omega \text{ has } e_i(z) = d, \\ 0 & \text{otherwise,} \end{cases}$$

where $z_{i,d}$ is a fixed (chosen) assignment with $e_i(z_{i,d}) = d$. The definition does not involve the design.
