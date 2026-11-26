# Diffusive transverse fluctuations of infinite-parent SLFV geodesics

**Setting.** Run the $\infty$-parent spatial Lambda-Fleming-Viot growth process (Poisson reproduction events $(t,z,r)$ of intensity $dt\otimes dz\otimes\mu(dr)$ with bounded radii, each event ball that meets the occupied region being added to it) from the single point $E=\{(0,0)\}$ until the first time it reaches the half-plane $\mathcal H^x=\{(x',y):x'\ge x\}$. A *geodesic* from $0$ to $\mathcal H^x$ is a chain of reproduction events, consecutive balls intersecting, starting from a ball containing the origin and whose ball at that hitting time meets $\mathcal H^x$; it traces the line of descent of the first individuals to reach distance $x$. Let $\mathcal L^{(r)}=\{(x',y):|y|\le r\}$.

**Theorem.**
1. For every $\varepsilon>0$ there is $A_\varepsilon<\infty$ such that for all $x>1$, with probability at least $1-\varepsilon$ some geodesic from $0$ to $\mathcal H^x$ stays inside $\mathcal L^{(A_\varepsilon\sqrt x)}$.
2. For every $\delta>0$ and $\beta\in(1/2,1]$ there is $c>0$ such that for all large $x$, with probability at least $1-\exp(-c\,x^{2\beta-1})$ some geodesic stays inside $\mathcal L^{(\delta x^\beta)}$.
3. For every $\varepsilon>0$ there is $a_\varepsilon>0$ such that for all large $x$, with probability at least $1-\varepsilon$ every geodesic from $0$ to $\mathcal H^x$ ends outside $\mathcal L^{(a_\varepsilon\sqrt x)}$.

The same $\sqrt x$ upper bound holds for geodesics from the half-plane $\{x'\le0\}$ to the point $(x,0)$.

## Expansion

The chains of reproduction events reaching $\mathcal H^x$ first can be encoded by a binary tree of candidate events, and a uniformly chosen *random geodesic path* through this tree is a geodesic. Along it the successive transverse displacements behave like weakly dependent, centred increments with exponential tails, and the number of steps is linear in $x$; a random-walk central limit picture then gives transverse wandering of order $\sqrt x$, with moderate-deviation tails $e^{-cx^{2\beta-1}}$ at scale $x^\beta$. This contrasts with first-passage percolation and KPZ-class growth, where geodesics fluctuate on the scale $x^{2/3}$. Genetically, the geodesic is the ancestral lineage of the pioneers, so the result says the ancestry of the leading edge of a two-dimensional expansion wanders diffusively sideways.

## Sources

- A. Louvet, M. I. Roberts, "Asymptotics for the growth of the infinite-parent Spatial Lambda-Fleming-Viot model", arXiv:2402.00601 (2024), Theorems 3 and 4, Definition 23, <https://doi.org/10.48550/arXiv.2402.00601>.
