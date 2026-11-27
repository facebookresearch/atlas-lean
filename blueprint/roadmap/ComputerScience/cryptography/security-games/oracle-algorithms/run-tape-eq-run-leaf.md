# A tape run applies its exits where the run stops

Fix a deterministic algorithm $e : M \times \mathrm{Rnd} \to C$ (typically encryption with explicit randomness), a default value $d$ and a continuation $K$ that maps an output $a$, a length $n'$ and a tape $\rho' \in \mathrm{Rnd}^{n'}$ to a value. For every oracle algorithm $c$, length $n$ and tape $\rho \in \mathrm{Rnd}^n$, the [tape run](run-tape.md) of $c$ on $\rho$ equals

- $d$ if the [stopping point](run-leaf.md) of the run is "none" (a query with no tape entry left), and
- $K(a, n', \rho')$ if the run stops with output $a$ and unused tape $\rho' \in \mathrm{Rnd}^{n'}$.
