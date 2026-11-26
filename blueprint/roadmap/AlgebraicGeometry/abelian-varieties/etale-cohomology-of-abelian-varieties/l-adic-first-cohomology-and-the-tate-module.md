# The ℓ-adic first cohomology of an abelian variety is the dual of its Tate module

Let $A$ be an [abelian variety](../abelian-scheme.md) over a separably closed field $k$ and $\ell$ a
prime different from the characteristic of $k$. Write
$H^1(A_{\mathrm{et}}, \mathbb{Z}_\ell) = \varprojlim_m H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$,
with the maps induced by the reductions $\mathbb{Z}/\ell^{m+1}\mathbb{Z} \to \mathbb{Z}/\ell^m\mathbb{Z}$,
and $T_\ell A = \varprojlim_m A_{\ell^m}(k)$, with multiplication by $\ell$ as transition maps. There
is a canonical isomorphism of $\mathbb{Z}_\ell$-modules

$$H^1(A_{\mathrm{et}}, \mathbb{Z}_\ell) \xrightarrow{\ \sim\ } \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell),$$

the limit over $m$ of the inverses of the bijections of
[First étale cohomology of an abelian variety with finite coefficients](first-etale-cohomology-with-finite-coefficients.md),
through the identification of $\operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell)$ with
$\varprojlim_m \operatorname{Hom}(A_{\ell^m}(k), \mathbb{Z}/\ell^m\mathbb{Z})$, which sends $\psi$ to the
family of maps induced by $\psi$ modulo $\ell^m$.

This is Milne's Theorem 12.1 (a), which is stated for a separably closed field; his Remark 12.5 also
says that Theorem 12.1 holds when $k$ is only separably closed, with a reference to his *Étale
Cohomology*, II 3.17. For the identification, multiplication by $\ell$ maps $A_{\ell^{m+1}}(k)$ onto
$A_{\ell^m}(k)$, as $\ell_A$ is finite, étale and surjective and $k$ is separably closed; so the
projection $T_\ell A \to A_{\ell^m}(k)$ is surjective with kernel $\ell^m T_\ell A$, and
$\operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell) = \varprojlim_m
\operatorname{Hom}(T_\ell A / \ell^m T_\ell A, \mathbb{Z}/\ell^m\mathbb{Z})$, with the transition
maps of the finite-level page.

## Depends on

- [Abelian scheme](../abelian-scheme.md), for abelian varieties over a field
- [The étale fundamental group and first étale cohomology with finite coefficients](../../grothendieck-topologies/etale-fundamental-group-and-first-cohomology.md),
  for the étale cohomology groups $H^1(A_{\mathrm{et}}, \mathbb{Z}/\ell^m\mathbb{Z})$

## Proof depends on

- [First étale cohomology of an abelian variety with finite coefficients](first-etale-cohomology-with-finite-coefficients.md),
  for the bijections at each level and their compatibility with the transition maps
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for $\ell_A$ finite, étale and
  surjective (its item 2)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 7.3, p. 34; Theorem 12.1 (a), p. 55; Remark 12.5, p. 56.
- J. S. Milne, *Lectures on Étale Cohomology*, course notes, version 2.21 (2013), <https://www.jmilne.org/math/CourseNotes/LEC.pdf>: §19, the convention
  $H^r(X, \mathbb{Z}_\ell) = \varprojlim H^r(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z})$, p. 126.
- J. S. Milne, *Étale Cohomology*, Princeton University Press, 1980: II 3.17, as cited by Milne,
  *Abelian Varieties*, p. 56 (not read).
