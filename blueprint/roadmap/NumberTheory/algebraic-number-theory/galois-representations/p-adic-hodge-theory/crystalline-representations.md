# Crystalline representations

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$
whose residue field $k$ is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$), and let
$K_0 = W(k)[1/p]$ be its maximal absolutely unramified subfield. Let $A_{\mathrm{cris}}$ be the $p$-adic completion of the divided power envelope
of $W(R)$ with respect to $\ker \theta$, and
$B_{\mathrm{cris}} = A_{\mathrm{cris}}[1/p][1/t] \subset B_{\mathrm{dR}}$. The ring $B_{\mathrm{cris}}$ is stable under
$G_K$ and carries the injective Frobenius $\varphi$ induced by the Witt vector Frobenius, which commutes with
$G_K$ and satisfies $\varphi(t) = pt$. The inclusion $B_{\mathrm{cris}} \subset B_{\mathrm{dR}}$ extends to an injective map
$K \otimes_{K_0} B_{\mathrm{cris}} \to B_{\mathrm{dR}}$, $B_{\mathrm{cris}}^{G_K} = K_0$, and $B_{\mathrm{cris}}$ is $(\mathbb{Q}_p, G_K)$-regular: a
nonzero $b \in B_{\mathrm{cris}}$ such that $G_K$ acts on the line $\mathbb{Q}_p b$ through a character is a unit.

A $p$-adic representation $V$ of $G_K$ is **crystalline** if it is $B_{\mathrm{cris}}$-admissible, that is,
$\dim_{K_0} D_{\mathrm{cris}}(V) = \dim_{\mathbb{Q}_p} V$ for $D_{\mathrm{cris}}(V) = (B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} V)^{G_K}$.
Then $D_{\mathrm{cris}}(V)$ is a filtered $\varphi$-module: $\varphi$ is a bijective Frobenius-semilinear
endomorphism, and $K \otimes_{K_0} D_{\mathrm{cris}}(V) = D_{\mathrm{dR}}(V)$ carries the Hodge filtration.

## Depends on

- [de Rham representations](de-rham-representations.md), for $R$, $\theta$, $t$, $B_{\mathrm{dR}}$ and its filtration
- [Admissible representations for a regular ring of periods](admissible-representations.md)

## Proof depends on

- [Structure of the rings of periods](structure-of-the-period-rings.md), for the injectivity of $K \otimes_{K_0} B_{\mathrm{cris}} \to B_{\mathrm{dR}}$ and the properties of $A_{\mathrm{cris}}$ (its item 2)
- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for the regularity of $B_{\mathrm{cris}}$

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §7.1, Definitions 7.1 and 7.3 ($A_{\mathrm{cris}}$), Proposition 7.6, Definition 7.7 ($B_{\mathrm{cris}}$), Proposition
  7.8 (injectivity of $K \otimes_{K_0} B_{\mathrm{cris}} \to B_{\mathrm{dR}}$, $B_{\mathrm{cris}}^{G_K} = K_0$); §8.1,
  Proposition 8.7 (regularity), (8.3), Definition 8.9 (crystalline), Proposition 8.10 (crystalline implies
  semistable), Proposition 8.11.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses crystalline representations as `Formalism.WeaklyAdmissibleFiltrations.IsCrys`, and at places of number
  fields as `GlobalTheory.Pst.IsCrysAt`. Three of the seven clauses of `GlobalTheory.Published.FontaineBcris` are
  statements of this page: the injectivity of $B_{\mathrm{cris}} \to B_{\mathrm{dR}}$ (`IotaInj`), the injectivity of
  $K \otimes_{K_0} B_{\mathrm{cris}} \to B_{\mathrm{dR}}$ over the finite extensions $K$ (`TensorInj`) and the regularity of
  $B_{\mathrm{cris}}$ (`Regular`); the other four are on the page on the
  [fundamental exact sequence](fundamental-exact-sequence.md).
