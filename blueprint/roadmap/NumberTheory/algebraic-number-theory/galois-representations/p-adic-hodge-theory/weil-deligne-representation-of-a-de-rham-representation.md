# Weil–Deligne representation of a de Rham representation

Let $K$ be a finite extension of $\mathbb{Q}_\ell$ with residue field $k$, and let $\rho$ be a de Rham
representation of $G_K$ on a finite-dimensional $\overline{\mathbb{Q}}_\ell$-vector space $V$. By the $p$-adic
monodromy theorem (here with $p = \ell$) there is a finite Galois extension $L/K$ such that
$(V \otimes_{\mathbb{Q}_\ell} B_{\mathrm{st}})^{G_L}$ is a free $\overline{\mathbb{Q}}_\ell \otimes_{\mathbb{Q}_\ell} L_0$-module of
rank $\dim V$, where $L_0$ is the maximal absolutely unramified subfield of $L$. Choose such an $L$ and an
embedding $\tau \colon L_0 \to \overline{\mathbb{Q}}_\ell$, and put

$$W = (V \otimes_{\tau, L_0} B_{\mathrm{st}})^{G_L} = (V \otimes_{\mathbb{Q}_\ell} B_{\mathrm{st}})^{G_L}
\otimes_{\overline{\mathbb{Q}}_\ell \otimes L_0, \, 1 \otimes \tau} \overline{\mathbb{Q}}_\ell.$$

For $\sigma \in W_K$ lying above the $m$-th power of the geometric Frobenius of $k$, set
$r(\sigma) = \rho(\sigma) \otimes (\sigma \varphi^{m [k : \mathbb{F}_\ell]})$, an automorphism of $W$, where $\varphi$ is the
Frobenius of $B_{\mathrm{st}}$. Then $\mathrm{WD}(V, \rho) = (W, r, 1 \otimes N)$ is a Weil–Deligne representation of
$W_K$ over $\overline{\mathbb{Q}}_\ell$; up to isomorphism it does not depend on the choices of $L$ and $\tau$, and
$\mathrm{WD}$ is a functor from de Rham representations of $G_K$ over $\overline{\mathbb{Q}}_\ell$ to Weil–Deligne
representations, compatible with restriction to open subgroups and with tensor operations.

## Depends on

- [Weil–Deligne representations](../weil-deligne-representations/weil-deligne-representations.md)
- [de Rham representations](de-rham-representations.md)
- [Semistable and potentially semistable representations](semistable-representations.md), for $B_{\mathrm{st}}$ with $\varphi$ and $N$
- [p-adic monodromy theorem](p-adic-monodromy-theorem.md), for the existence of $L$

## Sources

- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), arXiv:math/0412357 (version 2), §1, p. 4 (the construction of $\mathrm{WD}(V, \rho)$ for de Rham
  $(V, \rho)$, its independence of $L$ and $\tau$, functoriality, and compatibility with restriction and tensor
  operations, "due to Fontaine"; the existence of $L$ citing Berger).
- L. Berger, "An introduction to the theory of p-adic representations", arXiv:math/0210184 (version 1),
  §II.5.2 (the Weil–Deligne representation attached to a potentially semistable representation through
  $D_{\mathrm{st}}^L(V)$ with its $\operatorname{Gal}(L/K)$-action, defined by Fontaine).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses Weil–Deligne representations at the places above $\ell$ as `GlobalTheory.Pst.wdAt`.
