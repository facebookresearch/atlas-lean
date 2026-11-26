# A sign condition on principal minors excludes Turing bifurcation

Consider the $n$-component reaction–diffusion system $\partial_t u = D \nabla^2 u + f(u)$ with diagonal diffusion matrix $D = \operatorname{diag}(D_1, \dots, D_n)$, $D_i \ge 0$, and a homogeneous equilibrium $P$, $f(P) = 0$, that is stable without diffusion: every eigenvalue of $J = J_u f(P)$ has negative real part. A Fourier mode with $|k|^2 = \mu > 0$ evolves under $J - \mu D$. A **Turing instability** occurs when, as $\mu$ varies, a real eigenvalue of $J - \mu D$ crosses $0$, i.e. $\det(J - \mu D) = 0$ for some $\mu > 0$; a **wave instability** occurs when a pair of purely imaginary eigenvalues appears, i.e. $J - \mu D$ has eigenvalues $\pm i\omega$, $\omega \ne 0$, for some $\mu > 0$. For an increasing word $(i_1 < \dots < i_k)$, $M_{i_1 \dots i_k}$ is the principal minor of $J$ on rows and columns $i_1, \dots, i_k$.

**Theorem.** If $(-1)^k M_{i_1 \dots i_k} \ge 0$ for every $k = 1, \dots, n-1$ and every increasing word $(i_1, \dots, i_k)$, then $\det(J - \mu D) \ne 0$ for all $\mu > 0$ and all $D \ge 0$; hence $P$ cannot undergo a Turing bifurcation for any choice of diffusion rates.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Expanding the determinant multilinearly in the diagonal entries,

$$\det(J - \mu D) = \sum_{S \subseteq \{1, \dots, n\}} (-\mu)^{|S|} \Bigl(\prod_{i \in S} D_i\Bigr) M_{S^c},$$

with $M_\emptyset = 1$. Multiplying by $(-1)^n$, the term for $S$ becomes $\mu^{|S|} \prod_{i \in S} D_i \cdot (-1)^{n - |S|} M_{S^c} \ge 0$, and the term $S = \emptyset$ is $(-1)^n \det J > 0$ because a stable $J$ has $(-1)^n \det J > 0$. So $(-1)^n \det(J - \mu D) > 0$ for every $\mu > 0$. The theorem generalizes a result of Satnoianu et al. (2000) without assuming $J$ is S-stable, and says nothing about wave instabilities.

## Sources

- E. Villar-Sepúlveda and A. R. Champneys, *General conditions for Turing and wave instabilities in reaction–diffusion systems*, J. Math. Biol. 86 (2023), 39. <https://doi.org/10.1007/s00285-023-01870-3> (PMCID: PMC9884266) Section 2, Definition 1 and Theorem 1.
