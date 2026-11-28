# Local perturbation analysis of fast–slow reaction–diffusion systems

Consider a reaction–diffusion system with a slowly diffusing species $u$ and a rapidly diffusing species $v$,

$$\partial_tu=\delta\nabla^2u+f(u,v),\qquad \partial_tv=\nabla^2v+g(u,v),$$

on a bounded domain with no-flux boundary conditions. Local perturbation analysis (LPA) combines two formal limits: the slow species does not spread ($\delta\to0$), and the fast species mixes instantaneously, so that it is spatially uniform. These are distinct assumptions: sending $\delta\to0$ with the diffusivity of $v$ fixed at $1$ leaves $v$ a nonuniform field obeying its own diffusion equation, whereas LPA replaces it by a single global value. LPA follows a spike of infinitesimal width but finite height in $u$ placed on a homogeneous steady state. The PDE is replaced by the ODE system for global variables $(u,v)$ and a local variable $u_L$ at the spike:

$$\dot u=f(u,v),\qquad \dot v=g(u,v),\qquad \dot u_L=f(u_L,v).$$

The first two equations form the well-mixed system. Branches of LPA equilibria with $u_L=u$ are global branches (homogeneous states); branches with $u_L\ne u$ are local branches (patterns). Parameter regimes are classified as stable (only global branches are stable), polarizable (stable global and stable local branches coexist, so a sufficiently large perturbation forms a pattern) and unstable (all global branches unstable, so arbitrarily small perturbations form a pattern). For a model with $u$, $v$ and a slow third species $F$, the slow species also receive local copies.

## Expansion

With $\delta=0$ the slow species does not spread, so the spike evolves under the local kinetics; with instantaneous mixing the fast species seen by the spike is the shared global value $v$, and the spike's negligible width leaves that global pool unaffected. For a conserved system such as wave pinning, this uniform pool is what allows $v$ to be eliminated through the total amount. The Jacobian of the LPA system at a homogeneous steady state is block lower triangular, with the well-mixed Jacobian in one block and $\partial_uf$ in the other, so the LPA spectrum is the well-mixed spectrum plus $\partial_uf$. Numerical continuation of the LPA system detects the polarizable regime, a nonlinear (finite-amplitude) instability invisible to linear Turing analysis.

## Sources

- Y. Liu, E. G. Rens, L. Edelstein-Keshet, "Spots, stripes, and spiral waves in models for static and motile cells: GTPase patterns in cells", J. Math. Biol. 82 (2021), article 28, Sections 3.1–3.2, Equations (2a)–(2e), Appendix 8, <https://doi.org/10.1007/s00285-021-01550-0>, PMCID PMC7929972.
