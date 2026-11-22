# Lieb–Thirring kinetic energy inequality

For every dimension $d \ge 1$ there is a constant $K > 0$ such that for every $N$ and every family $u_1, \dots, u_N$ of smooth compactly supported complex functions on $\mathbb{R}^d$ that is orthonormal in $L^2(\mathbb{R}^d)$,

$$
K \int_{\mathbb{R}^d} \Big(\sum_n |u_n|^2\Big)^{1 + 2/d} \le \sum_n \int_{\mathbb{R}^d} |\nabla u_n|^2, \qquad |\nabla u|^2 = \sum_k |\partial_k u|^2
$$

(R. L. Frank, *The Lieb–Thirring inequalities: recent results and open problems*, arXiv:2007.09326v1, July 17, 2020 preprint, Theorem 1; E. H. Lieb and W. Thirring, Phys. Rev. Lett. 35 (1975) 687–689). This is Frank's Theorem 1 restricted from $H^1(\mathbb{R}^d)$ to smooth compactly supported functions, hence a weaker statement.

Here $\rho = \sum_n |u_n|^2$ is the one-particle density of the Slater determinant built from the $u_n$, and $\sum_n \int |\nabla u_n|^2$ is its kinetic energy in units where $\hbar^2/2m = 1$, without spin. The point is that $K_d$ does not depend on $N$: for a single function ($N = 1$) the inequality is a Gagliardo–Nirenberg inequality, and orthonormality, the Pauli principle, is what keeps the constant uniform in $N$. Frank's Open Problem 2 asks for the optimal $K_d$. By duality the inequality is equivalent to the bound $\sum_n |E_n(-\Delta + V)|^{\gamma} \le L_{\gamma, d} \int V_-^{\gamma + d/2}$ on the negative eigenvalues of Schrödinger operators with $\gamma = 1$ (Frank, Section 3.1, Theorem 9; the general moments are his Theorem 10); that eigenvalue form needs Schrödinger operators on $L^2(\mathbb{R}^d)$ and is not stated here.

The statement assumes the $u_n$ smooth with compact support, which makes every integral finite, so it is weaker than Frank's Theorem 1 for $H^1$ functions; its hypotheses are satisfiable, for instance with $N = 1$.

## Background

- [Gagliardo–Nirenberg inequality](gagliardo-nirenberg-inequality/README.md): the case of one function is an inequality of this type.
- [Sobolev embedding theorem](sobolev-embedding-theorem/README.md): the Lieb–Thirring inequality is a Sobolev inequality for orthonormal families.
- [Araki–Lieb–Thirring inequality](../../LinearAlgebra/positive-definite-matrices/araki-lieb-thirring-inequality/araki-lieb-thirring.md): the matrix trace inequality that Lieb and Thirring proved in their 1976 paper on the eigenvalue moments.

## Sources

- R. L. Frank, The Lieb–Thirring inequalities: recent results and open problems, arXiv:2007.09326v1 (preprint dated July 17, 2020), Theorems 1, 9 and 10. The theorem numbers refer to that preprint.
- E. H. Lieb and W. Thirring, Bound on kinetic energy of fermions which proves stability of matter, Phys. Rev. Lett. 35 (1975), 687–689.
