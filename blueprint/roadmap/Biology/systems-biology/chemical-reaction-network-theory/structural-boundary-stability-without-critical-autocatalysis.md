# Structural boundary stability without critical autocatalysis

Use the notation of [next-generation splitting of boundary steady states via ALT-graphs](next-generation-splitting-of-boundary-steady-states-via-alt-graphs.md): an integer-valued, binary reaction network satisfying (K1)-(K5), a siphon $\mathcal X$, a boundary steady state $c^*=(x^*,y^*)$ with $x^*=0$, and the ALT-graph $\mathcal G$ on $\mathcal X$ with its sets $\mathcal R_C$ of critical autocatalytic reactions and $\mathcal Z_C$ of critical strongly connected components. Assume that every vertex $X_i\in\mathcal X$ has a directed path to $0$ in $\mathcal G$, and that for every admissible choice of rate functions $c^*$ is locally asymptotically stable for the invariant subsystem on its boundary face within its stoichiometric compatibility class.

**Theorem.**

1. If $\mathcal R_C=\varnothing$ and $\mathcal Z_C=\varnothing$, then $c^*$ is locally asymptotically stable relative to its stoichiometric compatibility class $\mathsf C_{c^*}$ for every choice of kinetic rate functions satisfying (K1)-(K5). For mass action this holds for all rate constants $\kappa_k>0$.
2. If $\mathcal R_C\ne\varnothing$ or $\mathcal Z_C\ne\varnothing$, there is an autocatalytic decomposition $\mathcal G=\mathcal G_F\oplus\mathcal G_{-V}$ with $F=L(\mathcal G_F)$ nonnegative and nonzero, $V$ a $Z$-matrix with nonnegative inverse, and

$$\operatorname{rank}(FV^{-1})\le|\mathcal R_C|+|\mathcal Z_C|.$$

Thus only critical autocatalysis can destabilize the boundary, and the stability threshold $\rho(FV^{-1})=1$ is computed from a next-generation matrix of small rank. Worked examples in the source include the EnvZ-OmpR osmoregulation mechanism, a two-site bifunctional enzyme, the SIR model with reinfection, and a vector-borne disease model, where the boundary steady state is the disease-free equilibrium.

## Depends on

- [Next-generation splitting of boundary steady states via ALT-graphs](next-generation-splitting-of-boundary-steady-states-via-alt-graphs.md)

## Expansion

Intuitively, an autocatalytic loop that is not critical can be balanced inside the $Z$-matrix part of the splitting by an outgoing catalytic instance of the same reaction, so it never needs to enter $F$. When no critical object exists, the Jacobian of the reduced system is the negative of a $Z$-matrix with nonnegative inverse for every admissible choice of rate derivatives, and stability holds structurally. With critical autocatalysis, only one instance per critical reaction or critical component has to be placed in $F$, which bounds the rank of the next-generation matrix by the number of such objects.

## Sources

- M. D. Johnston and P. Jarne Cupons, "Autocatalysis and Boundary Stability in Chemical Reaction Systems", arXiv preprint (2026), <https://doi.org/10.48550/arXiv.2610.01636>. Corollary 3.11 (proved in Appendix E), Definition 3.5, and the examples of Section 4 (Examples 4.1-4.4).
