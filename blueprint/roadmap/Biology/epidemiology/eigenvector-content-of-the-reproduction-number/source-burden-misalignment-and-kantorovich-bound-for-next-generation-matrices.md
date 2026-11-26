# Source-burden misalignment and a Kantorovich bound for next-generation matrices

**Setting.** For an age- or group-structured epidemic with non-negative irreducible next-generation matrix $K$, $R_0=\rho(K)$ keeps only the Perron eigenvalue. The **right** Perron vector $v$ ($Kv=\rho v$) is the burden distribution (who gets infected in the growth phase), and the **left** Perron vector $w$ ($w^{\mathsf T}K=\rho w^{\mathsf T}$) is the source distribution, the reproductive value (who drives transmission). They coincide iff $K$ is normal. Measure their misalignment by the eigenvalue condition number and the angle
$$\kappa=\frac{\|v\|\,\|w\|}{w^{\mathsf T}v}=\frac1{\cos\theta}.$$

**Proposition (reciprocal contact).** Let $K=QC$ with $C$ symmetric, non-negative and irreducible (reciprocal contacts) and $Q=\operatorname{diag}(q_i)$, $q_i>0$ (age-specific susceptibility). Then:
1. $K=Q^{1/2}SQ^{-1/2}$ with $S=Q^{1/2}CQ^{1/2}$ symmetric, so the eigenvalues are real, $v=Q^{1/2}\varphi$ and $w=Q^{-1/2}\varphi$ for the unit Perron vector $\varphi>0$ of $S$;
2. with $p_i=\varphi_i^2$,
$$\kappa=\big(\mathbb E_p[q]\,\mathbb E_p[q^{-1}]\big)^{1/2};$$
3. with contrast $r=\max_iq_i/\min_iq_i$, the Kantorovich inequality gives
$$1\le\kappa\le\tfrac12\Big(\sqrt r+\tfrac1{\sqrt r}\Big),\qquad\theta\le\arccos\frac{2\sqrt r}{1+r},$$
with $\kappa=1$ iff susceptibility is uniform. The upper bound is attained when $q$ takes only its two extreme values with equal Perron mass, and is otherwise a strict supremum.

So under reciprocal contact, source-burden misalignment is controlled by the susceptibility contrast alone; misalignment beyond this bound in real matrices comes from contact asymmetry. Across 177 national synthetic contact matrices the operator is never normal, and with age-specific susceptibility the median source-burden angle is about $26^\circ$, exceeding $40^\circ$ in some countries, while transient (non-normal) amplification stays small.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Diagonal similarity to a symmetric matrix makes the Perron vectors explicit, $v\propto Q^{1/2}\varphi$ and $w\propto Q^{-1/2}\varphi$, so $w^{\mathsf T}v=\|\varphi\|^2=1$, $\|v\|^2=\sum q_i\varphi_i^2$ and $\|w\|^2=\sum q_i^{-1}\varphi_i^2$, which is the formula for $\kappa$. The Kantorovich inequality bounds $\mathbb E[q]\mathbb E[1/q]\le(m+M)^2/(4mM)$ for any probability weights on $[m,M]$. Policy consequence: minimizing $R_0$ is a problem about the source vector (protect those who spread), while minimizing deaths weights the burden vector by infection fatality (protect those who die), so the two objectives target different age groups, and lowering the scalar can raise average infection fatality. This motivates reporting $R_0$ together with its eigenvectors when contacts are structured and susceptibility is heterogeneous.

## Sources

- F. Sanchez, "What $R_0$ deletes: eigenvectors, non-normality, and the social content of the basic reproduction number", arXiv:2607.03979 (2026), Sections 2-3, Section 4 (Proposition 4.1), Sections 5-6 and Section 8, <https://doi.org/10.48550/arXiv.2607.03979>.
