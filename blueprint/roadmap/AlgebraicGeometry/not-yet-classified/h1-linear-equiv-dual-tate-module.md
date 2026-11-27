# The ℓ-adic H¹ of an abelian variety is the dual of its Tate module, Galois-equivariantly

Let $k$ be a field, $K$ a separable closure of $k$, $\ell$ a prime different from the
characteristic of $k$, and $A$ an abelian variety over $k$. Write $A(K)$ for the group of
$K$-points of $A$ and $T_\ell A = \varprojlim_n A(K)[\ell^n]$ for its Tate module. Then there is a
$\mathbb{Z}_\ell$-linear isomorphism

$$\varphi \colon H^1(A_K, \mathbb{Z}_\ell) \xrightarrow{\ \sim\ }
  \operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell)$$

compatible with the actions of $\operatorname{Gal}(K/k)$: for every $\sigma$, every
$x \in H^1(A_K, \mathbb{Z}_\ell)$ and every $t \in T_\ell A$,
$\varphi(\sigma x)(\sigma t) = \varphi(x)(t)$, that is,
$\varphi(\sigma x) = \varphi(x) \circ \sigma^{-1}$.

Here $H^1(A_K, \mathbb{Z}_\ell)$ is the cohomology of the pro-étale sheaf
$C(-, \mathbb{Z}_\ell)$ on $A_K = A \times_k \operatorname{Spec} K$, and $\sigma$ acts on it by
inverse image along $\mathrm{id}_A \times \operatorname{Spec} \sigma$. On $T_\ell A$, $\sigma$
acts through the induced map of Tate modules (`TateModule.map`) of any additive map $g$ of
$A(K)$ with $g(P) = \operatorname{Spec} \sigma \gg P$ for all $P$; exactly one such $g$ exists,
the action of $\sigma$ on points.

This is the degree-one case of Milne, *Abelian Varieties* (v2.0, 2008), Remark 12.5, p. 56,
the Galois compatibility of the isomorphism of Theorem 12.1(a), p. 55, stated through the
existence of a compatible isomorphism rather than for the canonical one; for $k$ separably closed
it is Theorem 12.1(a) in that existence form. The étale cohomology
$H^1(A_K, \mathbb{Z}_\ell) = \varprojlim_n H^1(A_K, \mathbb{Z}/\ell^n)$ of the source is read
through pro-étale cohomology, which computes it here.
