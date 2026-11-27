# Möbius fold circles and odd cusp counts in two-parameter fate landscapes

**Setting.** Let $X_\theta$ be a smooth family of vector fields on $\mathbb{R}^n$ (a gene-regulatory model) depending on a parameter $\theta\in\mathbb{R}^2$ (e.g. two morphogen levels), generic in the sense of singularity theory. The *catastrophe manifold*

$$\mathcal{M}=\{(x,\theta): X_\theta(x)=0\}\subset\mathbb{R}^n\times\mathbb{R}^2$$

is generically a smooth surface, and $\chi:\mathcal{M}\to\mathbb{R}^2$, $(x,\theta)\mapsto\theta$, has as its only local singularities folds (locally $(x_1,x_2)\mapsto(x_1^2,x_2)$) and cusps (normal form $\dot x=\pm x^3+\theta_1x+\theta_2$). Fold points form smooth curves in $\mathcal{M}$; a closed one is a *fold circle* $C$, and its image $\chi(C)$ is the bifurcation set $B_C$.

**Bundles.** At a fold point the one-dimensional centre manifold carries a definite flow direction, giving an orientation of its tangent line $\ell(\mathbf{x})$; along a closed curve $\Gamma\subset\mathcal{M}$ consisting of index-$1$ saddles or pseudo-hyperbolic attractors, the centre tangent lines form a line bundle $E^c_\Gamma\to\Gamma$, which is either a cylinder or a Möbius band. For a fold circle this is the *fold circle bundle* $\mathcal{C}_C$, and $C$ is called a *Möbius fold circle* if $\mathcal{C}_C$ is a Möbius band.

**Statements (generic families).**
1. On a fold curve whose endpoints are not cusps, the number of cusps equals the number of switches of the fold orientation.
2. $\mathcal{C}_C$ is a Möbius band if and only if $C$ contains an odd number of cusps.
3. For a fold circle $C$, the following are equivalent: (i) $C$ is Möbius; (ii) $C$ contains an odd number of cusps; (iii) there is a simple closed pseudo-hyperbolic curve $\Gamma\subset\mathcal{M}$ enclosing $C$ (and no other fold circle exterior to $C$) such that $\chi|_\Gamma$ double covers a curve in parameter space and $E^c_\Gamma$ is Möbius. Each of these implies (iv): $C$ lies in an open disk of $\mathcal{M}$ on which $\chi$ has degree $2$. In particular, no Möbius fold circle lies inside another fold circle.
4. A simple closed pseudo-hyperbolic curve $\Gamma$ with $E^c_\Gamma$ Möbius contains an odd number of Möbius fold circles in its interior.
5. *(Three-attractor decisions.)* If three smooth fold bifurcation curves $\ell_A,\ell_B,\ell_C$, one for each of three attractors, bound a region $\Delta$ in the configuration of the elliptic umbilic (as in a three-fate decision), then $\Delta$ contains $\chi(C)$ for a Möbius fold circle $C$, so in particular an odd number of cusps.

## Expansion

At a fold point the centre-manifold dynamics is $\dot x=\pm x^2+\dots$, so the flow direction orients $\ell(\mathbf{x})$ consistently along a cusp-free arc, and the normal form of the cusp shows the orientation reverses exactly at each cusp, giving statement 1. Going once around a fold circle, the fibres glue back with the original orientation precisely when the number of reversals is even, which is statement 2. The equivalences in statement 3 follow by deforming a small curve of saddles and attractors around $C$: its centre bundle is isotopic to the fold circle bundle, and over the exterior near $C$ each parameter value has two preimages, the saddle and the attractor that collide on $C$. For three-attractor regions, the elliptic-umbilic boundary behaviour forces the saddle bundle along the boundary to be Möbius, and statement 4 then produces the Möbius fold circle.

## Sources

- David A. Rand, Archishman Raju, Meritxell Saez, Francis Corson and Eric D. Siggia, "Geometry of gene regulatory dynamics", Proceedings of the National Academy of Sciences 118 (2021), e2109729118, <https://doi.org/10.1073/pnas.2109729118>; numbering as in arXiv:2105.13722: supplementary sections "Catastrophe Manifold", "Counting cusps on fold curves & circles" (fold orientation, fold circle bundle and the characterization theorem of Möbius fold circles) and "Topological charge and the elliptic umbilic".
