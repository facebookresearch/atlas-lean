# Primitive forms of type (k, ε) on Γ₀(N)

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$.
Write $S_k(N, \varepsilon)$ for the space of cusp forms of [type $(k, \varepsilon)$ on $\Gamma_0(N)$](../../modular-forms-of-type-k-epsilon.md) and
$f = \sum_{n \ge 1} a_n q^n$, $q = e^{2\pi i z}$, for their $q$-expansions. Besides the Hecke operators $T_p$, $p \nmid N$,
of that page, the operators $U_p$ act on $S_k(N, \varepsilon)$ for the primes $p \mid N$ by

$$f|U_p = \sum_{n \ge 1} a_{pn} q^n \qquad (p \mid N).$$

If $M$ divides $N$, $\varepsilon$ can be defined mod $M$, that is, $\varepsilon(d) = \varepsilon_M(d \bmod M)$ for a
Dirichlet character $\varepsilon_M$ mod $M$, and $d$ divides $N/M$, then $g \mapsto g(dz)$ maps $S_k(M, \varepsilon_M)$ into
$S_k(N, \varepsilon)$. The space of old forms
$S_k(N, \varepsilon)^{\mathrm{old}}$ is spanned by the $g(dz)$ for all such $M \ne N$, $g$ and $d$, and the space of new forms
$S_k(N, \varepsilon)^{\mathrm{new}}$ is its orthogonal complement for the Petersson inner product

$$\langle f, g \rangle = \int_D f(z)\, \overline{g(z)}\, y^k \, \frac{dx\, dy}{y^2},$$

where $z = x + iy$ and $D$ is a fundamental domain for $\Gamma_0(N)$ in the upper half-plane. A **primitive form** (newform)
of type $(k, \varepsilon)$ on $\Gamma_0(N)$ is a nonzero $f \in S_k(N, \varepsilon)^{\mathrm{new}}$ that is an eigenvector of all
the $T_p$, $p \nmid N$, normalized by $a_1 = 1$.

This is Li's definition of a normalized newform in her space $C_\varepsilon(N, 1) = S_k(N, \varepsilon)$, with the old forms
$G|B_d$, $(G|B_d)(z) = G(dz)$, of her §2. Li shows that a newform has $a_1 \ne 0$, so that it can be normalized, and that
a normalized newform is determined by its eigenvalues for the $T_p$, $p \nmid N$ (p. 294). Deligne and Serre refer for the
definition to Atkin and Lehner when $\varepsilon = 1$, and to Deligne, Li and Miyake in general (§1.7); the operators are
their (1.6.1) and (1.6.2).

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](../../modular-forms-of-type-k-epsilon.md), for cusp forms of type $(k, \varepsilon)$ and the operators $T_p$
- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the cusp forms of weight $k$ on $\Gamma_1(N)$
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)

## Proof depends on

This node has no prerequisites.

## Sources

- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: Introduction, pp. 285–286 (the spaces
  $C_\varepsilon(M, N)$ and their Hecke operators); §1, p. 287 (the operators $B_d$ and their effect on Fourier
  expansions); §2, p. 290 (the space $C_\varepsilon^-(M, N)$ spanned by the old forms) and pp. 293–294 (the Petersson inner
  product, the space $C_\varepsilon^+(M, N)$, the definition of newforms and of normalized forms, and the uniqueness of a
  normalized newform with given eigenvalues).
- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §1.5, pp. 508–509 (forms of type $(k, \varepsilon)$); §1.6,
  formulas (1.6.1)–(1.6.2), p. 509; §1.7, p. 509.
- A. O. L. Atkin and J. Lehner, *Hecke operators on $\Gamma_0(m)$*, Math. Ann. 185 (1970), 134–160, for $\varepsilon = 1$, as cited
  in Deligne–Serre (1974), §1.7, p. 509, and in Li (1975), p. 286; not read.
