# No unfilled shells in unrestricted Hartree–Fock theory

For molecular Coulomb systems, if the Hartree–Fock energy is attained, every eigenvalue of the Fock operator belonging to an eigenfunction orthogonal to the occupied orbitals lies strictly above every occupied orbital energy; in particular no degenerate level is partly filled.

Fix nuclei and suppose the Hartree–Fock energy is attained: some determinant $\Phi$ of an orthonormal admissible family $\varphi_1,\dots,\varphi_N$ with finite pair integrals minimizes $E_R$ among all determinants of such families. Choose the orbitals canonical (possible by the Hartree–Fock equations), with orbital energies $\varepsilon_1,\dots,\varepsilon_N$ and Fock form $f$ on $\mathcal D$. If $\varphi\in\mathcal D$ is normalized, orthogonal to every $\varphi_k$, and satisfies $f(\chi,\varphi)=\varepsilon\langle\chi,\varphi\rangle$ for all $\chi\in\mathcal D$, then $\varepsilon>\varepsilon_k$ for every $k=1,\dots,N$, and more precisely

$$
\varepsilon-\varepsilon_k\ge J_{k\varphi}-K_{k\varphi}=\frac12\iint\frac{|\varphi_k(x)\varphi(x')-\varphi(x)\varphi_k(x')|^2}{|r-r'|}\,dx\,dx'>0 .
$$

The statement concerns eigenfunctions in $\mathcal D$, not a separation from arbitrary continuous spectrum, and existence of a minimizer is a hypothesis.

## Context

Research (established). Bach, Lieb, Loss and Solovej proved the result for any one-body potential and any positive definite two-body interaction, contrary to the textbook picture of open-shell atoms in unrestricted Hartree–Fock theory; this page states the molecular Coulomb case, for which positivity of the pair term is pointwise.

## Depends on

- [Hartree–Fock equations](hartree-fock-equations.md)
- [Fock operator](fock-operator.md)

## Proof depends on

- [Energy of a Slater determinant](hartree-fock-energy-of-a-determinant.md)
- [Energy form of Slater determinants](../slater-determinants-and-second-quantization/energy-form-of-slater-determinants.md)

## Expansion

Replace $\varphi_k$ by $\varphi$ once. By the energy formula, $0\le E_R(\tilde\Phi)-E_R(\Phi)=\varepsilon-\varepsilon_k-(J_{k\varphi}-K_{k\varphi})$, using $\varepsilon_k=h_{kk}+\sum_j(J_{kj}-K_{kj})$ and $\varepsilon=h_{\varphi\varphi}+\sum_j(J_{\varphi j}-K_{\varphi j})$. Expanding the square shows $J_{k\varphi}-K_{k\varphi}$ equals the displayed integral, whose integrand is nonnegative and not almost everywhere zero (the antisymmetrized product of two orthonormal orbitals has norm $\sqrt2$), so it is positive. No second variation is needed.

## Sources

- Volker Bach, Elliott H. Lieb, Michael Loss and Jan Philip Solovej, *There are no unfilled shells in unrestricted Hartree-Fock theory*, Phys. Rev. Lett. 72 (1994) 2981–2983, <https://doi.org/10.1103/PhysRevLett.72.2981>; numbers from arXiv:cond-mat/9307066v1, Theorem, Eq. (5) and the proof following it. <https://arxiv.org/abs/cond-mat/9307066v1>
