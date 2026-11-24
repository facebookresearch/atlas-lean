# Weil–Deligne representation of a de Rham representation

Let $K$ be a finite extension of $\mathbb{Q}_\ell$ with residue field $k$, $f = [k : \mathbb{F}_\ell]$, and let
$\rho$ be a de Rham representation of $G_K$ on a finite-dimensional $\overline{\mathbb{Q}}_\ell$-vector space $V$. By
the $p$-adic monodromy theorem (here with $p = \ell$) there is a finite Galois extension $L/K$ such that

$$D = (V \otimes_{\mathbb{Q}_\ell} B_{\mathrm{st}})^{G_L}$$

is a free $\overline{\mathbb{Q}}_\ell \otimes_{\mathbb{Q}_\ell} L_0$-module of rank $\dim V$, where $L_0$ is the maximal
absolutely unramified subfield of $L$. On $D$ the Frobenius $\varphi_D = 1 \otimes \varphi$ is semilinear with respect
to the absolute Frobenius of $L_0$ and **bijective**, since $D$ is a $(\varphi, N)$-module over $L_0$ (the Frobenius
$\varphi$ of $B_{\mathrm{st}}$ itself is only injective); $N_D = 1 \otimes N$ satisfies $N_D \varphi_D = \ell \varphi_D N_D$;
and $G_K$ acts on $D$ through $\operatorname{Gal}(L/K)$ by $\rho \otimes (\text{action on } B_{\mathrm{st}})$,
semilinearly over $L_0$ and commuting with $\varphi_D$ and $N_D$. For $\sigma \in W_K$ lying above the $m$-th power of
the geometric Frobenius of $k$, with $m \in \mathbb{Z}$, the composite

$$r_D(\sigma) = (\rho(\sigma) \otimes \sigma) \circ \varphi_D^{m f}$$

is $\overline{\mathbb{Q}}_\ell \otimes L_0$-linear, the negative powers of $\varphi_D$ being taken on $D$. Choose an embedding
$\tau \colon L_0 \to \overline{\mathbb{Q}}_\ell$ and put
$W = D \otimes_{\overline{\mathbb{Q}}_\ell \otimes L_0, \, 1 \otimes \tau} \overline{\mathbb{Q}}_\ell$, with
$r(\sigma) = r_D(\sigma) \otimes 1$. Then $\mathrm{WD}(V, \rho) = (W, r, N_D \otimes 1)$ is a Weil–Deligne representation
of $W_K$ over $\overline{\mathbb{Q}}_\ell$; up to isomorphism it does not depend on the choices of $L$ and $\tau$, and
$\mathrm{WD}$ is a functor from de Rham representations of $G_K$ over $\overline{\mathbb{Q}}_\ell$ to Weil–Deligne
representations, compatible with restriction to open subgroups and with tensor operations.

## Depends on

- [Weil–Deligne representations](../weil-deligne-representations/weil-deligne-representations.md)
- [de Rham representations](de-rham-representations.md)
- [Semistable and potentially semistable representations](semistable-representations.md), for $B_{\mathrm{st}}$ with $\varphi$ and $N$
- [p-adic monodromy theorem](p-adic-monodromy-theorem.md), for the existence of $L$

## Proof depends on

- [Admissible representations for a regular ring of periods](admissible-representations.md), for the dimension criterion and the exact tensor functor $D_{B_{\mathrm{st}}}$ on representations of $G_L$, which give the rank of $D$, the bijectivity of the injective semilinear map $\varphi_D$ on it, and the compatibility with tensor operations
- [Weil group of a p-adic field](../weil-deligne-representations/weil-group-of-a-p-adic-field.md), for the geometric Frobenius and $\lvert \sigma \rvert = q^{-m}$ for $\sigma$ above its $m$-th power, which give the linearity of $r_D(\sigma)$ and, with $N_D \varphi_D = \ell \varphi_D N_D$, the relation $r(\sigma) N r(\sigma)^{-1} = \lvert \sigma \rvert N$

## Sources

- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), arXiv:math/0412357 (version 2), §1, p. 4 (the construction of $\mathrm{WD}(V, \rho)$ for de Rham
  $(V, \rho)$ as $(W, r, 1 \otimes N)$ with $r(\sigma) = \rho(\sigma) \otimes (\sigma \varphi^{m[k(v_K) : \mathbb{F}_l]})$, its
  independence of $L$ and $\tau$, functoriality, and compatibility with restriction and tensor operations, "due to
  Fontaine"; the existence of $L$ citing Berger).
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  Lemma 8.12 and Definition 8.13 ($D_{\mathrm{st}}(V)$ is a $(\varphi, N)$-module, whose Frobenius is bijective).
- L. Berger, "An introduction to the theory of p-adic representations", arXiv:math/0210184 (version 1),
  §II.5.2 (the Weil–Deligne representation attached to a potentially semistable representation through
  $D_{\mathrm{st}}^L(V)$ with its $\operatorname{Gal}(L/K)$-action, defined by Fontaine).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses Weil–Deligne representations at the places above $\ell$ as `GlobalTheory.Pst.wdAt`.
