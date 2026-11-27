# RPA equation for an input–output node pair

**Setting.** A biochemical network has nodes $P_1, \dots, P_n$ (molecular concentrations or activity states) with smooth rate functions

$$\dot P_k = f_k(P_1, \dots, P_n; I), \qquad k = 1, \dots, n,$$

where a scalar stimulus $I$ enters only the rate of a designated *input node* $P_{\mathrm{in}}$ (so $\partial f_k / \partial I = 0$ for $k \ne \mathrm{in}$, and $\partial f_{\mathrm{in}}/\partial I \ne 0$), and a designated *output node* $P_{\mathrm{out}}$ (possibly equal to the input node) is the end point of interest. Let $\pi_n(I) = (P_1^*, \dots, P_n^*)$ be a steady state depending smoothly on $I$ and let

$$J_n = \frac{\partial(f_1, \dots, f_n)}{\partial(P_1, \dots, P_n)}\Big|_{\pi_n}$$

be the Jacobian there. Let $M_{IO}$ be the $(n-1) \times (n-1)$ minor of $J_n$ obtained by deleting the row of the input node's rate $f_{\mathrm{in}}$ and the column of the output node $P_{\mathrm{out}}$.

The network has *robust perfect adaptation* (RPA) if $P_{\mathrm{out}}^*$ is independent of $I$ over the input range, for open sets of parameters (no fine tuning).

**Statement.** RPA occurs only when, for all $I$,

$$\det(M_{IO}) = 0 \qquad \text{(the RPA equation)},$$

$$\det(J_n) \ne 0 .$$

The determinant expansion of $\det(M_{IO})$ is a signed sum of at most $(n-1)!$ terms; each term is a product of a *route factor* (a chain of interactions from the input node to the output node), *circuit products* (multi-node feedback loops disjoint from the route), and *kinetic multipliers* $\partial f_k / \partial P_k$ (single-node cycles). RPA requires these terms to sum to zero for every $I$ while $\det J_n \ne 0$.

## Expansion

Differentiate the steady-state equations $f(\pi_n(I); I) = 0$ in $I$:

$$J_n \, \frac{d\pi_n}{dI} = -\frac{\partial f}{\partial I} = -\frac{\partial f_{\mathrm{in}}}{\partial I}\, e_{\mathrm{in}} .$$

With $\det J_n \ne 0$ (a nondegenerate steady state, as required for it to vary smoothly with $I$), Cramer's rule gives

$$\frac{dP^*_{\mathrm{out}}}{dI} = -\frac{\partial f_{\mathrm{in}}}{\partial I}\,\frac{C_{\mathrm{in},\mathrm{out}}}{\det J_n}, \qquad C_{\mathrm{in},\mathrm{out}} = (-1)^{\mathrm{in}+\mathrm{out}} \det(M_{IO}),$$

where $C_{\mathrm{in},\mathrm{out}}$ is the cofactor of entry $(\mathrm{in}, \mathrm{out})$. Since $\partial f_{\mathrm{in}}/\partial I \ne 0$, the output steady state is input-independent exactly when $\det(M_{IO})$ vanishes for all $I$. This is the input–output special case of the internal model principle's algebraic test for RPA to constant inputs (equivalent to integral control). Expanding the minor by the Leibniz formula and grouping permutation cycles gives the route, circuit and kinetic-multiplier structure of each term.

## Sources

- R. P. Araujo, L. A. Liotta, "The topological requirements for robust perfect adaptation in networks of any size", *Nature Communications* 9 (2018). Results, "General schema for identifying RPA topologies"; Methods, "Methods overview and relationship to the IMP" (RPA equation, Eq. 1; nondegeneracy, Eq. 2; derivations in Supplementary Note 2). <https://doi.org/10.1038/s41467-018-04151-6>. PMCID: PMC5931626.
