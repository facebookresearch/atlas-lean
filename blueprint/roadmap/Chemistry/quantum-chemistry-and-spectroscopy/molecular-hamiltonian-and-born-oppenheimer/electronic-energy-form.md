# Electronic energy form

The electronic energy form is the quadratic-form version of the clamped-nuclei Hamiltonian: it assigns a real energy to every admissible antisymmetric state with square-integrable weak gradients and absolutely convergent Coulomb terms, and its infimum is the electronic ground-state energy.

Fix nuclei as for the clamped-nuclei electronic Hamiltonian (pairwise distinct positions $R_A$, charges $Z_A\ge1$) and $N\ge1$. Write $x_i=(r_i,s_i)\in\mathbb R^3\times\{\uparrow,\downarrow\}$, $v(r)=-\sum_AZ_A|r-R_A|^{-1}$, $V_{\mathrm{ext}}=\sum_iv(r_i)$ and $W=\sum_{i<j}|r_i-r_j|^{-1}$. A state is a family $\Psi=(\psi_s)_{s\in\{\uparrow,\downarrow\}^N}$ of functions $\psi_s:(\mathbb R^3)^N\to\mathbb C$.

**Admissible states.** $\mathcal A_N$ is the set of states such that (i) for every $s$, the real and imaginary parts of $\psi_s$ lie in the real Sobolev space $H^1(\mathbb R^{3N})$; (ii) $\Psi$ is antisymmetric: permuting electron positions and their spin labels together multiplies $\Psi$ by the sign of the permutation, almost everywhere; (iii) for every $s$ and every pair $i<j$, $\int|\psi_s|^2|r_i-r_j|^{-1}\,dr<\infty$. The set $\mathcal A_N(R)\subseteq\mathcal A_N$ additionally requires $\int|\psi_s|^2|r_i-R_A|^{-1}\,dr<\infty$ for all $s$, $i$, $A$. Both are complex vector spaces. With $N=1$, elements of $\mathcal A_1(R)$ are the **admissible spin-orbitals**.

**Forms.** For $\Phi,\Psi\in\mathcal A_N(R)$ the energy form is

$$
\mathcal E_R(\Phi,\Psi)=\sum_{s}\int_{\mathbb R^{3N}}\Bigl(\frac12\sum_{i=1}^{N}\overline{\nabla_{r_i}\phi_s}\cdot\nabla_{r_i}\psi_s+\bigl(V_{\mathrm{ext}}+W\bigr)\,\overline{\phi_s}\,\psi_s\Bigr)dr ,
$$

a Hermitian sesquilinear form whose integrals converge absolutely; $E_R(\Psi)=\mathcal E_R(\Psi,\Psi)$ is real. For $N=1$ this is the **one-electron form** $h(\phi,\chi)$ (no $W$ term). The **electronic ground-state energy** is

$$
E_{\mathrm{el}}(R)=\inf\{E_R(\Psi):\Psi\in\mathcal A_N(R),\ \textstyle\sum_s\|\psi_s\|_{L^2}^2=1\}\in[-\infty,\infty),
$$

and the nuclear repulsion $V_{NN}(R)$ may be added as a constant. The normalized admissible set is nonempty, so $E_{\mathrm{el}}(R)<+\infty$; no attainment of the infimum is part of the definition.

## Context

Undergraduate (energy expression) and graduate (form domain). For Coulomb potentials, Hardy's inequality shows that conditions (iii) and the nuclear condition are automatic for $H^1$ states and that $E_R$ is bounded below on normalized states, so $E_{\mathrm{el}}(R)$ is finite; this is the form-domain description of Lewin, Lieb and Seiringer, recorded here as context rather than used. Quantum-chemistry methods, including the algorithms reviewed by Cao, Aspuru-Guzik and coauthors, approximate $E_{\mathrm{el}}(R)$.

## Depends on

- [Clamped-nuclei electronic Hamiltonian](clamped-nuclei-electronic-hamiltonian.md)
- [Sobolev space $H^1(U)$](../../../Analysis/partial-differential-equations/weak-solutions-of-elliptic-equations/mem-h1-on.md)

## Proof depends on

- [Cauchy–Schwarz inequality in an inner product space](../../../Analysis/hilbert-spaces/inner-product-spaces-and-their-completions/cauchy-schwarz.md)
- [Slater determinant](../slater-determinants-and-second-quantization/slater-determinant.md)

## Expansion

A definition. Absolute convergence: the gradient terms by the Cauchy–Schwarz inequality in $L^2$, and each Coulomb term by $|\overline{\phi}\psi|\le\frac12(|\phi|^2+|\psi|^2)$ applied term by term. Hermiticity is termwise conjugation. Closure under linear combinations uses $|\phi+\psi|^2\le2|\phi|^2+2|\psi|^2$. Nonempty witness: choose real smooth functions $u_1,\dots,u_N$ with unit $L^2$ norm supported in pairwise disjoint balls, and let $\Psi$ be the Slater determinant of $u_k\otimes\uparrow$; it is normalized (orthonormal orbitals), antisymmetric, smooth and compactly supported, hence each spin component has real and imaginary parts in $H^1$, and it is bounded with compact support, so every Coulomb integral is finite because $|r|^{-1}$ is locally integrable in $\mathbb R^3$ (Fubini in the remaining variables). Formally $\mathcal E_R(\Phi,\Psi)=\langle\Phi,\hat H_{\mathrm{el}}\Psi\rangle$ when $\Psi$ is a Schwartz function, by integrating the Laplacian by parts.

## Sources

- Mathieu Lewin, Elliott H. Lieb and Robert Seiringer, *Universal Functionals in Density Functional Theory*, chapter in *Density Functional Theory — Modeling, Mathematical Analysis, Computational Methods, and Applications*; numbers from arXiv:1912.10424v4, §1, Eqs. (2)–(3) (energy space and quadratic-form ground-state energy). <https://arxiv.org/abs/1912.10424v4>
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.1, Eq. (6). <https://arxiv.org/abs/1812.09976v2>
