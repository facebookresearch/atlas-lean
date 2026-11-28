# Structural identifiability of linear reaction–advection–diffusion models

**Setting.** A linear reaction–advection–diffusion (RAD) model has $m$ species densities $u_1, \dots, u_m$ on an interval, each with its own diffusion and advection coefficients and linear reaction terms coupling the species, and only a linear combination (for instance the total density) is observed. A parameter, or parameter combination, is *structurally identifiable* if it is determined by the noise-free observation for generic initial conditions. The differential-algebra approach eliminates the unobserved states to obtain an *input–output equation*, a polynomial relation among partial derivatives of the observed output, whose coefficients are the identifiable combinations.

**Theorem.**
1. Every linear RAD model with $m$ states reduces to polynomial input–output relations involving derivatives of order at most $4(m-1)$ in the output.
2. The identifiable parameter combinations of a linear spatially homogeneous model (the ODE obtained without advection and diffusion) form a subset of the identifiable combinations of every corresponding spatially heterogeneous model with linear advection and/or diffusion and general unknown initial conditions. Adding spatial structure never loses identifiability.
3. *(Example: cell-cycle model.)* For cells in two phases, $r_t = D_1 r_{xx} - k_1 r + 2k_2 g$ and $g_t = D_2 g_{xx} + k_1 r - k_2 g$, observed only through $n = r + g$, the input–output equation is

$$0 = -k_1 k_2\, n + (k_1 + k_2)\, n_t + n_{tt} - (D_2 k_1 + D_1 k_2)\, n_{xx} - (D_1 + D_2)\, n_{xxt} + D_1 D_2\, n_{xxxx},$$

so $k_1 k_2$, $k_1 + k_2$, $D_2 k_1 + D_1 k_2$, $D_1 + D_2$ and $D_1 D_2$ are identifiable, and hence all four parameters are locally identifiable, whereas without diffusion only $k_1 k_2$ and $k_1 + k_2$ are.

## Expansion

Applying the linear differential operators of the model to the observed combination and eliminating each unobserved species costs at most a fixed number of extra derivatives in $x$ and $t$, which gives the order bound. Setting all spatial derivatives of the output to zero in the input–output equation recovers the input–output equation of the homogeneous ODE, so its coefficients remain identifiable; the extra spatial terms can only add identifiable combinations, as the cell-cycle example shows, where distinct diffusivities of the two phases make the transition rates individually recoverable.

## Sources

- A. P. Browning, M. Tască, C. Falcó, R. E. Baker, "Structural identifiability analysis of linear reaction-advection-diffusion processes in mathematical biology", *Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences* 480(2286) (2024), 20230911, Theorem 1 and Corollary 1, cell-cycle example, <https://doi.org/10.1098/rspa.2023.0911> (preprint arXiv:2309.15326).
