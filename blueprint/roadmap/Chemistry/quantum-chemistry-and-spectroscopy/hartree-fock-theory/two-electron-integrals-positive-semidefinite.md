# Positive semidefiniteness of the two-electron integral matrix

Arranged as a matrix indexed by orbital pairs, the real electron-repulsion integrals form a positive semidefinite matrix, because the Coulomb kernel is a positive definite interaction; in particular exchange integrals are nonnegative.

Let $\chi_1,\dots,\chi_n:\mathbb R^3\to\mathbb R$ be real functions with all products $\chi_i\chi_j\in L^1\cap L^{6/5}(\mathbb R^3)$ (true, for example, for Gaussian basis functions). Define the $n^2\times n^2$ matrix indexed by ordered pairs $I=(i,j)$, $L=(k,l)$

$$
V_{IL}=(ij|kl)=\iint\frac{\chi_i(r_1)\chi_j(r_1)\,\chi_k(r_2)\chi_l(r_2)}{|r_1-r_2|}\,dr_1dr_2 .
$$

Then $V$ is real symmetric and positive semidefinite, and $V=LL^{\mathsf T}$ for some real lower-triangular $L$ (a Cholesky factorization with possibly zero pivots). The rows $(i,j)$ and $(j,i)$ coincide, so $V$ is singular whenever $n\ge2$; singularity is routine. **Exchange corollary:** if spin-orbitals $\varphi_i,\varphi_j$ have spin-summed product $f(r)=\sum_s\overline{\varphi_j(r,s)}\varphi_i(r,s)$ in $L^1\cap L^{6/5}(\mathbb R^3)$, then their exchange integral satisfies $K_{ij}\ge0$.

## Context

Graduate. This underlies the Cholesky and low-rank factorizations of the two-electron tensor used to reduce the cost of classical and quantum simulations of chemistry. For $H^1$ orbitals the product condition follows from the Sobolev embedding $H^1(\mathbb R^3)\subset L^2\cap L^6$.

## Depends on

- [Coulomb and exchange integrals](coulomb-and-exchange-integrals.md)

## Proof depends on

None.

## Expansion

With the unitary angular-wavenumber Fourier transform $\hat f(k)=(2\pi)^{-3/2}\int e^{-ik\cdot x}f(x)\,dx$, for $f\in L^1\cap L^{6/5}$ one has $D(f,f)=\iint\overline{f(r_1)}f(r_2)|r_1-r_2|^{-1}dr_1dr_2=4\pi\int|\hat f(k)|^2|k|^{-2}dk\ge0$: prove it for Schwartz $f$ from $\widehat{|x|^{-1}}=\sqrt{2/\pi}\,|k|^{-2}$ in this convention, then extend by density using the Hardy–Littlewood–Sobolev inequality $|D(f,g)|\le C\|f\|_{6/5}\|g\|_{6/5}$. Apply it to $f=\sum_{k,l}c_{kl}\chi_k\chi_l$ for the quadratic form, and to the spin-summed product for $K_{ij}=D(f,f)$. A positive semidefinite real matrix has a Cholesky factorization with zero pivots allowed (for example $L$ from the LDL decomposition of $V+\epsilon I$ and a compactness limit $\epsilon\to0$). Missing prerequisites on the graph: the Fourier transform of $|x|^{-1}$, the Hardy–Littlewood–Sobolev inequality and the semidefinite Cholesky factorization.

## Sources

- Douglas W. O'Neal and Jack Simons, *Application of Cholesky-like Matrix Decomposition Methods to the Evaluation of Atomic Orbital Integrals and Integral Derivatives*, Int. J. Quantum Chem. 36 (1989) 673–688, Abstract and Eqs. (1)–(2) (citing N. H. F. Beebe and J. Linderberg, Int. J. Quantum Chem. 12 (1977) 683). [simons.hec.utah.edu/papers/131.pdf](https://simons.hec.utah.edu/papers/131.pdf)
