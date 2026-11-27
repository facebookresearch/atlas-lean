# Oscillatory cores from unstable feedbacks

**Setting.** Work with a reaction network under parameter-rich kinetics and its Child-Selection (CS) matrices $\mathbb S[\boldsymbol\kappa]$: square stoichiometric submatrices pairing each selected species with a reaction it feeds, with negative diagonal. A matrix $A$ is *D-Hopf* if some invertible principal submatrix changes inertia under two different positive diagonal rescalings. A matrix is $P^-$ if every $k\times k$ principal minor has sign $(-1)^k$, and $P^-_0$ if every nonzero one does. *Unstable cores* are CS-matrices minimal with respect to being Hurwitz-unstable; a $k\times k$ unstable core is an *unstable-positive feedback* if $\operatorname{sign}\det\mathbb S[\boldsymbol\kappa]=(-1)^{k-1}$ (one real positive eigenvalue) and an *unstable-negative feedback* if $\operatorname{sign}\det\mathbb S[\boldsymbol\kappa]=(-1)^k$ (only a complex pair with positive real part). An *oscillatory core* is a D-Hopf CS-matrix none of whose proper principal submatrices is D-Hopf.

**Matrix criteria.**
- (Proposition 9.5) If some principal submatrix of $A$ is D-Hopf, then $A$ is D-Hopf.
- (Proposition 9.8) If some principal submatrix $A[\kappa]$ is Hurwitz-stable but not $P^-_0$, then $A$ is D-Hopf.
- (Corollary 9.13) If some $k\times k$ principal submatrix is an invertible Hurwitz-unstable $P^-_0$ matrix with a Hurwitz-stable $(k-1)\times(k-1)$ principal submatrix, then $A$ is D-Hopf.

**Network recipes.**
- (Corollary 11.6, class I) A Hurwitz-stable CS-matrix containing an unstable-positive feedback (for instance an autocatalytic core) as a principal submatrix is D-Hopf.
- (Corollary 11.10, class II) A $k\times k$ unstable-negative feedback with a Hurwitz-stable $(k-1)\times(k-1)$ principal submatrix is D-Hopf.
- (Proposition 11.2) Every D-Hopf CS-matrix contains an invertible principal submatrix that is an oscillatory core.

Combined with the D-Hopf criterion for periodic orbits, any nondegenerate network containing an oscillatory core admits periodic solutions for suitable parameters.

## Depends on

- [D-Hopf Jacobians force periodic orbits](d-hopf-jacobians-force-periodic-orbits.md)

## Expansion

Proposition 9.8: if $A[\kappa]$ is not $P^-_0$, some principal minor $A[\kappa']$ has sign $(-1)^{k'-1}$, so $A[\kappa']$ has an odd number of positive real eigenvalues. Scaling the coordinates outside $\kappa'$ by $\varepsilon\to0$ makes $A[\kappa]D(\varepsilon)$ unstable, while $D=I$ leaves it stable; the inertia changes. An unstable-positive feedback is not $P^-_0$, which gives the class I recipe (Lemma 11.5). For class II, the Fisher–Fuller theorem (Theorem 9.10) rescales a matrix with a nested chain of principal minors of signs $(-1)^j$ to have only negative real simple eigenvalues; Proposition 9.12 instead rescales a matrix with $\operatorname{sign}\det A=(-1)^n$ and a stable $(n-1)$-principal submatrix to be Hurwitz-stable, so the unstable-negative feedback is stabilized by one rescaling and unstable at the identity. Because unstable-negative feedbacks typically need many monomolecular steps before instability appears, class II oscillators obey a minimum-length requirement (the principle of length).

## Sources

- A. Blokhuis, P. F. Stadler, N. Vassena, "Stoichiometric recipes for periodic oscillations in reaction networks", *Proceedings of the Royal Society A Mathematical Physical and Engineering Science* 482(2340) (2026), 20250886, Propositions 9.5, 9.8, 9.12, 11.2, Theorem 9.10, Lemma 11.5 and Corollaries 9.13, 11.6, 11.10, <https://doi.org/10.1098/rspa.2025.0886> (preprint arXiv:2508.15273).
