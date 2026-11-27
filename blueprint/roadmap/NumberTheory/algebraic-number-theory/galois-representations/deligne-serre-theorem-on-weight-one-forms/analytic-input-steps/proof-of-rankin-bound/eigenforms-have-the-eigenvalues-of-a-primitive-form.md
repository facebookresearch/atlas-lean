# A Hecke eigenform of type (k, ε) has the eigenvalues of a primitive form

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$, and let
$f \ne 0$ be a cusp form of [type $(k, \varepsilon)$ on $\Gamma_0(N)$](../../modular-forms-of-type-k-epsilon.md) that is an eigenvector of all the Hecke
operators $T_p$, $p \nmid N$, with $f|T_p = a_p f$. Then there are a divisor $M$ of $N$ such that $\varepsilon$ can be
defined mod $M$, that is, $\varepsilon(d) = \varepsilon_M(d \bmod M)$ for a Dirichlet character $\varepsilon_M$ mod $M$, and a
[primitive form](primitive-forms-of-type-k-epsilon.md) $f_0 = \sum_{n \ge 1} b_n q^n$ of type $(k, \varepsilon_M)$ on
$\Gamma_0(M)$, with $b_1 = 1$, such that $b_p = a_p$ for every prime $p \nmid N$. The level $M$ may be a proper divisor of
$N$.

Deligne and Serre use this to reduce Rankin's bound to primitive forms ("On se ramène aussitôt au cas où $f$ est une forme
primitive", Démonstration 5.2), through their §1.9: every form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ is, uniquely,
$E(z) + \sum_i \lambda_i f_i(d_i z)$, with $E$ an Eisenstein series and $f_i$ primitive of type $(k, \varepsilon)$ on
$\Gamma_0(N_i)$, where $\varepsilon$ can be defined mod $N_i$ (the $f_i$ are of type $(k, \varepsilon_{N_i})$ at their own
level), $N_i \mid N$ and $d_i \mid N/N_i$. In Li's terms: the new and old
subspaces of $S_k(N, \varepsilon)$ are stable under the $T_p$, $p \nmid N$, so the component of $f$ in each is an eigenvector
with the same eigenvalues, or is $0$. A nonzero new component is a newform, which can be normalized; otherwise $f$ is old,
and an eigenvector in the old space has the eigenvalues of a newform of a smaller level (Li, p. 294).

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](../../modular-forms-of-type-k-epsilon.md), for cusp forms of type $(k, \varepsilon)$ and the operators $T_p$
- [Primitive forms of type (k, ε) on Γ₀(N)](primitive-forms-of-type-k-epsilon.md)
- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the stability of the old and new subspaces under the $T_p$, $p \nmid N$: the $T_p$ commute with $g \mapsto g(dz)$ (Li,
  p. 287), and $\langle f|T_p, g \rangle = \varepsilon(p) \langle f, g|T_p \rangle$ (Li, p. 294, after Petersson);
- that a newform has a nonzero first coefficient (Li, Theorem 2, p. 292, and p. 294);
- that an eigenvector of the $T_p$, $p \nmid N$, in the old space has the eigenvalues of a newform of a level $M \mid N$,
  $M \ne N$ (Li, p. 294, by induction on the number of prime factors of the level), or the decomposition of §1.9 of
  Deligne–Serre with its uniqueness.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §1.9, p. 510; Démonstration 5.2, p. 518.
- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: §1, p. 287 (the commutation of $T_p$
  with $B_d$); Theorem 2, p. 292; pp. 293–294 (the Petersson inner product, the invariance of $C_\varepsilon^+(M, N)$ under
  $T_p$, and the equivalence of an eigenform in $C_\varepsilon^-(M, N)$ with a newform of lower level).
