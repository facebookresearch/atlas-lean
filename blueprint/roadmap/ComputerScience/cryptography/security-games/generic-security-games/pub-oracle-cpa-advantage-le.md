# Eavesdropping bounds give CPA bounds

Suppose $\mathrm{Enc}_{pk}(m)$ is the distribution of $E(pk, m, \rho)$ for $\rho$ uniform on a finite
nonempty set, and let $A$ be a chosen-plaintext adversary that makes at most $n$ encryption queries.
If the simulating eavesdropper built from $A$, $E$ and $n$ has eavesdropping advantage at most
$\varepsilon$, then $A$ has CPA advantage at most $\varepsilon$.
