# N-representability of electron densities

Every nonnegative density with integral $N$ and finite von Weizsäcker kinetic energy is the one-particle density of an $N$-electron Slater determinant with finite kinetic energy.

Let $N\ge1$ and $\rho:\mathbb R^3\to[0,\infty)$ be measurable with $\int\rho=N$ and $\sqrt\rho\in H^1(\mathbb R^3)$, that is $\sqrt\rho\in L^2$ with weak gradient in $L^2$. Then there exist orthonormal functions $\phi_1,\dots,\phi_N$, with real and imaginary parts in $H^1(\mathbb R^3)$, such that

$$
\sum_{k=1}^{N}|\phi_k(r)|^2=\rho(r)\quad\text{for almost every }r .
$$

Assigning spin up to every $\phi_k$, the Slater determinant of the spin-orbitals $\phi_k\otimes\uparrow$ is an antisymmetric wave function with density $\rho$ and finite kinetic energy. Conversely, the density of every normalized antisymmetric state of finite kinetic energy has $\sqrt\rho\in H^1$ (Hoffmann-Ostenhof inequality), so these are exactly the densities of normalized antisymmetric states with finite kinetic energy (finite-kinetic $N$-representability). No claim is made about finiteness of Coulomb pair integrals of the constructed determinant.

## Context

Graduate. Due to Lieb, following Gilbert and Harriman; it shows that the constrained-search functional is defined on every physically reasonable density.

## Depends on

- [Slater determinant](../slater-determinants-and-second-quantization/slater-determinant.md)
- [Sobolev space $H^1(U)$](../../../Analysis/partial-differential-equations/weak-solutions-of-elliptic-equations/mem-h1-on.md)

## Proof depends on

None.

## Expansion

Harriman–Lieb construction: let $m(x)=\iint\rho(x,y,z)\,dy\,dz$ and $\theta(x)=\frac{2\pi}{N}\int_{-\infty}^{x}m(t)\,dt$, and set $\phi_k(r)=\sqrt{\rho(r)/N}\,e^{ik\theta(x)}$ for $k=0,1,\dots,N-1$. Then $\sum_k|\phi_k|^2=\rho$, and orthonormality follows from $\int\frac{\rho}{N}e^{i(k-l)\theta(x)}dr=\frac1N\int m(x)e^{i(k-l)\theta(x)}dx=\delta_{kl}$ by the change of variables $u=\theta(x)$ (the pushforward of $m\,dx$ is Lebesgue measure on $[0,2\pi)$ times $N/2\pi$, so flat portions of $\theta$ need no invertibility). For regularity, applying the $L^2(\mathbb R^2)$ norm to $\sqrt\rho(x,\cdot)$ gives $\sqrt m\in H^1(\mathbb R)$; one-dimensional Sobolev embedding gives $m$ bounded, so $\theta$ is Lipschitz, and the Leibniz and chain rules give $\phi_k\in H^1$ with $\nabla\phi_k=e^{ik\theta}(\nabla\sqrt{\rho/N}+ik\theta'(x)\sqrt{\rho/N}\,e_x)$. The determinant has finite kinetic energy by the tensor-product rule. Converse (Hoffmann-Ostenhof): for each particle $i$ write $\rho_i(x)=\sum_s\int|\Psi_s|^2\prod_{j\ne i}dx_j$; taking the $L^2$ norm of $\Psi$ in the other variables gives $|\nabla\sqrt{\rho_i}|^2\le\sum_s\int|\nabla_{x_i}\Psi_s|^2\prod_{j\ne i}dx_j$, and the Euclidean-norm inequality for $\sqrt{\rho}=\|(\sqrt{\rho_1},\dots,\sqrt{\rho_N})\|$ gives $\int|\nabla\sqrt\rho|^2\le\sum_i\int|\nabla\sqrt{\rho_i}|^2$, bounded by $2T$ under the kinetic-energy convention $T=\frac12\sum_i\sum_s\int_{\mathbb R^{3N}}|\nabla_{x_i}\Psi_s|^2$. Missing prerequisites on the graph: weak derivatives of $L^2$-norm maps, one-dimensional Sobolev embedding, the weak chain rule with Lipschitz phases, the tensor-product rule, and the Hoffmann-Ostenhof inequality.

## Sources

- Mathieu Lewin, Elliott H. Lieb and Robert Seiringer, *Universal Functionals in Density Functional Theory*, chapter in *Density Functional Theory — Modeling, Mathematical Analysis, Computational Methods, and Applications*; numbers from arXiv:1912.10424v4, §1, Theorem 1 with Eqs. (4)–(6), and §4.3, Eqs. (43)–(44) (explicit phases). <https://arxiv.org/abs/1912.10424v4>
- Erik Tellgren, Simen Kvaal and Trygve Helgaker, *Fermion N-representability for prescribed density and paramagnetic current density*, arXiv:1310.1246v2, §I (density-only result and references). <https://arxiv.org/abs/1310.1246v2>
