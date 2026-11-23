# Semistable and potentially semistable representations

Let $K$ be a finite extension of $\mathbb{Q}_p$ with maximal absolutely unramified subfield $K_0$. Let
$\varpi \in R$ be an element with $\varpi^{(0)} = p$ and $u = \log[\varpi] \in B_{\mathrm{dR}}^+$. The ring of
**semistable periods** is $B_{\mathrm{st}} = B_{\mathrm{cris}}[u] \subset B_{\mathrm{dR}}$; $u$ is transcendental over
$B_{\mathrm{cris}}$, so $B_{\mathrm{st}}$ is a polynomial ring over $B_{\mathrm{cris}}$. It is stable under $G_K$, the
Frobenius extends by $\varphi(u) = pu$, and the **monodromy operator** $N$ is the $B_{\mathrm{cris}}$-derivation
with $N(u) = -1$; then $N \varphi = p \varphi N$, $N$ commutes with $G_K$, and
$0 \to B_{\mathrm{cris}} \to B_{\mathrm{st}} \xrightarrow{N} B_{\mathrm{st}} \to 0$ is exact. The map
$K \otimes_{K_0} B_{\mathrm{st}} \to B_{\mathrm{dR}}$ is injective, $B_{\mathrm{st}}^{G_K} = K_0$, and $B_{\mathrm{st}}$ is
$(\mathbb{Q}_p, G_K)$-regular.

A $p$-adic representation $V$ is **semistable** if it is $B_{\mathrm{st}}$-admissible, that is,
$\dim_{K_0} D_{\mathrm{st}}(V) = \dim V$ for $D_{\mathrm{st}}(V) = (B_{\mathrm{st}} \otimes V)^{G_K}$; then $D_{\mathrm{st}}(V)$
is a filtered $(\varphi, N)$-module, with $K \otimes_{K_0} D_{\mathrm{st}}(V) = D_{\mathrm{dR}}(V)$. Crystalline
representations are semistable, and semistable representations are de Rham. $V$ is **potentially
semistable** if there is a finite extension $K'/K$ in $\bar K$ such that $V|_{G_{K'}}$ is semistable; potentially
semistable representations are de Rham, since $B_{\mathrm{dR}}$-admissibility over $G_{K'}$ implies it over $G_K$.

## Depends on

- [Crystalline representations](crystalline-representations.md), for $B_{\mathrm{cris}}$ and its Frobenius
- [de Rham representations](de-rham-representations.md), for $R$, $B_{\mathrm{dR}}$ and $D_{\mathrm{dR}}$
- [Admissible representations for a regular ring of periods](admissible-representations.md)

## Proof depends on

- [Structure of the rings of periods](structure-of-the-period-rings.md), for the logarithm on $[R^\times]$ and the transcendence of $u$ (its item 2)
- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for the regularity of $B_{\mathrm{st}}$

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §7.2, Definition 7.11, Proposition 7.14 ($u$ transcendental); §8.1, Definition 8.1 ($B_{\mathrm{st}} = B_{\mathrm{cris}}[u]$,
  $u = \log[\varpi]$), Theorems 8.3 and 8.4, (8.1), Definition 8.5 ($N$), Proposition 8.6, Proposition 8.7,
  Definition 8.9, Proposition 8.10; §8.3, Definition 8.46, Remark 8.47, Proposition 8.48 and Definition 8.49
  (potentially semistable representations, which are de Rham).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses potentially semistable representations as `GlobalTheory.Pst.IsPstAt`.
