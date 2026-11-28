# LPA instability coincides with Turing instability as slow diffusion vanishes

Let $\partial_tu=\delta\nabla^2u+f(u,v)$, $\partial_tv=\nabla^2v+g(u,v)$ have a homogeneous steady state $(u_*,v_*)$, and let

$$J_{WM}=\begin{pmatrix}\partial_uf&\partial_vf\\\partial_ug&\partial_vg\end{pmatrix}$$

be the well-mixed Jacobian there. In the limit $\delta\to0$, the following are equivalent:

1. $(u_*,v_*)$ is Turing unstable: $\operatorname{tr}J_{WM}<0$, $\det J_{WM}>0$, and $\det\big(J_{WM}-Dq^2\big)<0$ for some $q^2>0$, with $D=\operatorname{diag}(0,1)$;
2. $(u_*,v_*)$ is a stable equilibrium of the well-mixed system and an unstable equilibrium of the local perturbation analysis system;
3. $\operatorname{tr}J_{WM}<0$, $\det J_{WM}>0$ and $\partial_uf(u_*,v_*)>0$.

Consequently the LPA-unstable regime is exactly the Turing-unstable regime, while LPA-stable and LPA-polarizable regimes are both Turing stable.

## Depends on

- [Local perturbation analysis of fast–slow reaction–diffusion systems](local-perturbation-analysis-of-fast-slow-reaction-diffusion.md)

## Proof depends on

- [Local perturbation analysis of fast–slow reaction–diffusion systems](local-perturbation-analysis-of-fast-slow-reaction-diffusion.md)

## Expansion

Item 1 is the [Turing](../turing-patterns-and-diffusion-driven-instability/README.md) condition with the slow diffusivity set to $0$ and the fast one kept at $1$, while item 2 uses the LPA system, in which the fast species is uniform; the theorem says the two limits give the same instability criterion. The first two Turing conditions say the steady state is stable for the well-mixed system. With $\delta=0$,

$$\det\big(J_{WM}-Dq^2\big)=\det J_{WM}-q^2\,\partial_uf,$$

which is linear in $q^2$, so it becomes negative for some $q^2>0$ exactly when $\partial_uf>0$. The LPA Jacobian is block lower triangular with diagonal blocks $J_{WM}$ and $\partial_uf$, so its eigenvalues are those of $J_{WM}$ together with $\partial_uf$; given well-mixed stability, LPA instability is equivalent to $\partial_uf>0$. A general version for more species is due to Holmes (2014).

## Sources

- Y. Liu, E. G. Rens, L. Edelstein-Keshet, "Spots, stripes, and spiral waves in models for static and motile cells: GTPase patterns in cells", J. Math. Biol. 82 (2021), article 28, Appendix 8, conditions (5a)–(5c), <https://doi.org/10.1007/s00285-021-01550-0>, PMCID PMC7929972.
