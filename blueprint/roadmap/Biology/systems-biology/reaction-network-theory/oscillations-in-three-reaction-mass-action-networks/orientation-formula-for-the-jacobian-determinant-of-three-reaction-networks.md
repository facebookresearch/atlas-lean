# Orientation formula for the Jacobian determinant of three-reaction networks

**Setting.** Consider a mass-action network with $n$ species, three reactions and rank two (an
$(n,3,2)$ network), dynamically nontrivial so that $\ker\Gamma$ of the stoichiometric matrix
$\Gamma \in \mathbb{R}^{n\times 3}$ is spanned by a vector $u \in \mathbb{R}^3_{+} \cup \mathbb{R}^3_{-}$.
Let $\Gamma_l \in \mathbb{R}^{n\times 3}$ be the source matrix (column $j$ is the source complex of
reaction $j$) with rows $a_{i\cdot}$. Choose two rows $c, d$ of $\Gamma$ spanning its row space and
write $\Gamma = \tilde\Gamma\,[c;\,d]$ with $\tilde\Gamma \in \mathbb{R}^{n\times 2}$ of rank two and top
block the identity; then $u = c \times d$. At a positive equilibrium $\bar x$ there is $\mu \ne 0$ with
$\kappa \circ \bar x^{\Gamma_l^{\mathsf T}} = \mu u$.

**Statement.** The reduced Jacobian determinant (the determinant of the Jacobian acting on the
stoichiometric subspace) at $\bar x$ is

$$\det J_{\mathrm{red}} = \mu |\mu|\, |u_1 u_2 u_3| \sum_{i<j} \frac{\tilde\Gamma[\{i,j\},\{1,2\}]}{\bar x_i \bar x_j}\,\big(\mathbf 1 \cdot (a_{i\cdot} \times a_{j\cdot})\big),$$

where $\tilde\Gamma[\{i,j\},\{1,2\}]$ is the $2\times 2$ minor of $\tilde\Gamma$ on rows $i, j$. For two
species this reduces to

$$\det J = \frac{\mu |\mu|\, |u_1 u_2 u_3|}{\bar x_1 \bar x_2}\,\big(\mathbf 1 \cdot (a_{1\cdot} \times a_{2\cdot})\big).$$

Consequently, in a planar three-reaction system: (i) a nonzero Jacobian determinant requires the three
source complexes to be affinely independent (span a triangle); (ii) $\det J > 0$ if and only if the
three reaction vectors span a triangle with the same orientation as the triangle of source complexes;
(iii) if the orientations are opposite, every positive equilibrium is a saddle and the system has no
periodic orbit. More generally, a rank-two mass-action system without trivial species in which every
positive equilibrium is a saddle (negative reduced Jacobian determinant) has no periodic orbit, since a
periodic orbit on a two-dimensional stoichiometric class must surround an equilibrium that is not a
saddle.

## Expansion

The reduced Jacobian in the local coordinates given by $\tilde\Gamma$ is
$\mu\, [c^{\mathsf T};\, d^{\mathsf T}]\,\Delta_u\, \Gamma_l^{\mathsf T}\, \Delta_{1/\bar x}\, \tilde\Gamma$,
a product of a $2\times 3$, a $3\times n$ and an $n\times 2$ factor; the Cauchy–Binet formula expands
its determinant over pairs of species, and each term factors into a minor of $\tilde\Gamma$ times the
triple product $\mathbf 1\cdot(a_{i\cdot}\times a_{j\cdot})$, which is the signed area of the sources
projected onto species $i, j$. The identity $\mu u_k = |\mu u_k|$ (all $u_k$ share the sign of $\mu$)
turns the remaining factors into $\mu|\mu||u_1u_2u_3|$. In the planar case $\operatorname{sgn}\det J =
\operatorname{sgn}\mu = \operatorname{sgn}u_k$ once the sources are positively oriented, so the sign of
$u = c \times d$, the orientation of the reaction vectors, decides between saddles and possible
oscillators. The paper's (4,3,2) example with $u_1=u_2=u_3=-1$ has all positive equilibria saddles and
hence no periodic orbit.

## Sources

- M. Banaji, B. Boros, J. Hofbauer, "Oscillations in three-reaction quadratic mass-action systems", Studies in Applied Mathematics (2024), <https://doi.org/10.1111/sapm.12639> (PMC10953466). Section 2.5 (reduced Jacobian determinant), Section 3.1 (saddles rule out periodic orbits), Section 3.3, Eqs. (7) and (8), Lemma 2.
