# The simulation is exact for each challenge bit

Suppose $\mathrm{Enc}_{pk}(m)$ is the distribution of $E(pk, m, \rho)$ for $\rho$ uniform on a finite
nonempty set, and let $A$ be a chosen-plaintext adversary that makes at most $n$ encryption queries.
For each challenge bit $b$, the left-or-right eavesdropping experiment of the simulating
eavesdropper built from $A$, $E$ and $n$ has the same distribution as the left-or-right
chosen-plaintext experiment of $A$.
