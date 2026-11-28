# Running a simulated tape run

Let $O : Q \to A$ be a keyed function, $\mathrm{encQ}$, $d$ and $K$ as in the [simulation](sim-tape.md). For every oracle algorithm $c$ (queries in $M$, answers in $C$), length $n$ and tape $\rho \in \mathrm{Rnd}^n$, running the simulation of $c$ on $\rho$ against $O$ equals the [tape run](run-tape.md) of $c$ on $\rho$ with

- encryption algorithm $(m, r) \mapsto$ the run of $\mathrm{encQ}(m, r)$ against $O$,
- default $d$, and
- continuation $(a, n', \rho') \mapsto$ the run of $K(a, n', \rho')$ against $O$.

Both the per-query encryption and the terminal continuation are interpreted by running against $O$; the default is the same value $d$ on both sides.
