# Reaching the origin under a rational piecewise affine map of the plane is undecidable

No algorithm decides, given a rational piecewise affine map of the plane and a rational starting point, whether some iterate of the point is the origin.

A map $\mathbb{R}^n \to \mathbb{R}^m$ is *affine linear* if it is a linear map plus a constant vector. A map $f\colon \mathbb{R}^n \to \mathbb{R}^m$ is *piecewise affine linear* if $\mathbb{R}^n$ can be partitioned into finitely many subsets $U_i$, each defined by finitely many affine linear inequalities, such that $f|_{U_i}$ agrees with an affine linear map depending on $i$; it is *rational* if all coefficients of the affine linear polynomials involved are rational. Let $f^k$ be the $k$-th iterate of $f$.

**Theorem (Moore).** There is no algorithm that decides, given a rational piecewise affine linear map $f\colon \mathbb{R}^2 \to \mathbb{R}^2$ and a point $\vec{a} \in \mathbb{Q}^2$, whether there exists $k$ such that $f^k(\vec{a}) = \vec{0}$.

Here both the map and the starting point are part of the input, and the dimension is two.

## Depends on

None.

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The survey states the theorem without proof, under the observation that many nonlinear dynamical systems can simulate universal Turing machines and hence provide undecidable problems. The proof, in Moore's paper, simulates a universal Turing machine by a piecewise affine map of the plane, so that the orbit of the point encoding the initial configuration reaches the origin exactly when the machine halts; it reduces the halting problem for Turing machines, through a simulation that has no page.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in arXiv:1204.0299v2 (the definitions and the problem "Point goes to origin in finite time" in Section 10.1 of arXiv:1204.0299v2).
- Cristopher Moore, *Unpredictability and undecidability in dynamical systems*, Physical Review Letters 64 (1990), no. 20, 2354–2357, https://doi.org/10.1103/PhysRevLett.64.2354, the original source, cited for attribution beside Bjorn Poonen's survey above.
