# Møller–Plesset second-order energy

In Møller–Plesset perturbation theory with real canonical Hartree–Fock orbitals and a gap between occupied and virtual orbital energies, the formal zeroth- and first-order terms together reproduce the reference energy and the formal second-order coefficient is a sum over double excitations.

Fix nuclei and real orthonormal admissible spin-orbitals $\varphi_1,\dots,\varphi_M$ with finite pair integrals that are canonical Hartree–Fock orbitals for the occupied set $\{\varphi_1,\dots,\varphi_N\}$, $1\le N\le M$, in the finite-basis sense: $f(\varphi_p,\varphi_q)=\varepsilon_p\delta_{pq}$ for all $p,q\le M$. Assume the gap condition $\varepsilon_i<\varepsilon_a$ for all occupied $i\le N$ and virtual $a>N$. In the basis write $\hat H=\hat H_0+\hat V$ with $\hat H_0=\sum_p\varepsilon_pa_p^\dagger a_p$ and $\hat V=\hat H-\hat H_0$. Then the Hartree–Fock determinant $|0\rangle=\Phi$ spans the eigenspace of the simple lowest eigenvalue of $\hat H_0$ on the $N$-particle sector. In the real orthonormal determinant basis of that sector, ordered with $\Phi$ first, $\hat H_0$ is the diagonal matrix $\mathrm{diag}(d)$ and $\hat V$ a real symmetric matrix $H_1$; the formal Rayleigh–Schrödinger coefficients $E^{(1)}=\mathrm{pertE1}(H_1)$ and $E^{(2)}=\mathrm{pertE2}(d,H_1,0)$ of the linked definitions, with $E^{(0)}=d_0$, evaluate to

$$
E^{(0)}=\sum_{i\le N}\varepsilon_i,\qquad E^{(0)}+E^{(1)}=E_R(\Phi),\qquad E^{(2)}=-\sum_{i<j\le N}\ \sum_{N<a<b\le M}\frac{\langle ij\|ab\rangle^2}{\varepsilon_a+\varepsilon_b-\varepsilon_i-\varepsilon_j},
$$

where $\langle ij\|ab\rangle=g_{ijab}-g_{ijba}$ (real). In particular $E^{(2)}\le0$, and $E^{(2)}=0$ when fewer than two virtual orbitals exist. That these formal coefficients are the Taylor coefficients of the lowest eigenvalue of $\hat H_0+t\hat V$ at $t=0$ is standard nondegenerate perturbation theory and is not asserted here. Here $E_R(\Phi)$ is the energy of the given reference determinant, which is the Hartree–Fock energy only if that determinant is a minimizer.

## Context

Graduate. MP2 is the cheapest correlated method; in quantum algorithms its amplitudes initialize unitary coupled-cluster parameters. A positive double-excitation gap alone does not make the reference nondegenerate: for $N=2$ and orbital energies $(0,1,1,3)$ the determinants $\{1,2\}$ and $\{1,3\}$ tie, which is why the occupied–virtual gap is assumed. Complex orbitals need the Hermitian version with $|\langle ij\|ab\rangle|^2$.

## Depends on

- [Fock operator](../hartree-fock-theory/fock-operator.md)
- [Second-quantized electronic Hamiltonian](../slater-determinants-and-second-quantization/second-quantized-electronic-hamiltonian.md)
- [Slater–Condon rules for two-electron operators](../slater-determinants-and-second-quantization/slater-condon-rules-two-electron.md)
- [First-order energy correction](../variational-method-perturbation-theory-and-h-cke/pert-e1.md)
- [Second-order energy correction](../variational-method-perturbation-theory-and-h-cke/pert-e2.md)

## Proof depends on

- [Matrix elements of the second-quantized Hamiltonian](../slater-determinants-and-second-quantization/second-quantized-hamiltonian-matrix-elements.md)
- [Brillouin's theorem](../hartree-fock-theory/brillouin-theorem.md)
- [Energy of a Slater determinant](../hartree-fock-theory/hartree-fock-energy-of-a-determinant.md)

## Expansion

$\hat H_0$ is diagonal in the determinant basis with eigenvalue the sum of occupied orbital energies; any determinant other than $\Phi$ replaces some occupied orbitals by virtual ones and, by the gap, has strictly larger eigenvalue, so all energy denominators are nonzero. All matrices are real symmetric (real orbitals), so the definitions apply with $H_1=\hat V$ and $H_2=0$. $E^{(1)}=(H_1)_{00}=\langle0|\hat V|0\rangle$ gives $E_R(\Phi)-\sum_i\varepsilon_i$ by the matrix-element correspondence and the energy formula. In $\mathrm{pertE2}=\sum_{K\ne0}(H_1)_{K0}^2/(d_0-d_K)$ only determinants $K$ with $\langle K|\hat V|0\rangle\ne0$ contribute: single excitations vanish by Brillouin's theorem (and $\hat H_0$ is diagonal), triple and higher by the Slater–Condon rules, and doubles give $\langle ab\|ij\rangle$ with denominator $\varepsilon_i+\varepsilon_j-\varepsilon_a-\varepsilon_b<0$.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §VIII.C, Eqs. (107)–(133) (pp. 76–82). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
