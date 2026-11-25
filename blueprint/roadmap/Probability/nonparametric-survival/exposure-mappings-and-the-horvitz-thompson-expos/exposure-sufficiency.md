# Exposure Sufficiency

Let $U$ be a set of units, $\Omega$ a set of assignments, $e : U \times \Omega \to \Delta$ an exposure mapping and $y^r : U \times \Omega \to \mathbb R$ the randomization potential outcomes, $y^r_i(z)$ being the outcome of unit $i$ under assignment $z$. The exposure mapping is sufficient (properly specified, a design-free form of Condition 1 of Aronow and Samii (2017)) if each unit's outcome depends on the assignment only through its exposure: for every unit $i$ and all assignments $z, z'$,

$$e_i(z) = e_i(z') \implies y^r_i(z) = y^r_i(z').$$

The condition is required at every assignment, not only on the support $\{z : p_z > 0\}$ of a design; individual SUTVA is not assumed.
