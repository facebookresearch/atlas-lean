# de Rham representations

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, that is, a complete discretely valued field of
characteristic $0$ whose residue field $k$ is perfect of characteristic $p$ (for instance a finite extension of
$\mathbb{Q}_p$), let $C$ be the completion of $\bar K$, and let
$R = \varprojlim_{x \mapsto x^p} \mathcal{O}_{\bar K}/p$, a perfect ring of characteristic $p$, with the surjection
$\theta \colon W(R)[1/p] \to C$. The ring $B_{\mathrm{dR}}^+ = \varprojlim_n W(R)[1/p]/(\ker \theta)^n$ is the
$(\ker \theta)$-adic completion of $W(R)[1/p]$; it is a complete discrete valuation ring with residue field $C$, on
which $G_K$ acts. Two topologies on it must be distinguished: the topology of the discrete valuation, for which
the residue field $C$ is discrete, and the canonical topology, the inverse limit of the quotient topologies that
$W(R)[1/p]$ induces on the quotients $W(R)[1/p]/(\ker \theta)^n$, which is weaker and induces on $C$ its $p$-adic
topology. The action of $G_K$ is continuous for the canonical topology, which is the one used for continuous
cohomology. Let $\varepsilon = (1, \zeta_p, \zeta_{p^2}, \dots) \in R$ for a compatible system of primitive
$p^n$-th roots of unity; then $t = \log[\varepsilon]$ is a uniformizer of $B_{\mathrm{dR}}^+$ with
$g(t) = \chi(g) t$ for $g \in G_K$. The **field of $p$-adic periods** is
$B_{\mathrm{dR}} = \operatorname{Frac} B_{\mathrm{dR}}^+ = B_{\mathrm{dR}}^+[1/t]$, with the decreasing filtration
$\operatorname{Fil}^i B_{\mathrm{dR}} = t^i B_{\mathrm{dR}}^+$, $i \in \mathbb{Z}$; then
$\operatorname{gr} B_{\mathrm{dR}} \cong B_{\mathrm{HT}}$ and $B_{\mathrm{dR}}^{G_K} = K$, and $B_{\mathrm{dR}}$ is
$(\mathbb{Q}_p, G_K)$-regular.

A $p$-adic representation $V$ of $G_K$ is **de Rham** if it is $B_{\mathrm{dR}}$-admissible, that is,
$\dim_K D_{\mathrm{dR}}(V) = \dim_{\mathbb{Q}_p} V$ for $D_{\mathrm{dR}}(V) = (B_{\mathrm{dR}} \otimes_{\mathbb{Q}_p} V)^{G_K}$.
Then $D_{\mathrm{dR}}(V)$ is a filtered $K$-vector space with
$\operatorname{Fil}^i D_{\mathrm{dR}}(V) = (\operatorname{Fil}^i B_{\mathrm{dR}} \otimes V)^{G_K}$, and
$D_{\mathrm{dR}}^+(V) = \operatorname{Fil}^0 D_{\mathrm{dR}}(V)$. Every de Rham representation is Hodge–Tate, and
$\operatorname{gr}^i D_{\mathrm{dR}}(V) \cong (C(i) \otimes V)^{G_K}$ for every $i$. The de Rham representations
form a sub-Tannakian category on which $D_{\mathrm{dR}}$ is an exact faithful tensor functor to filtered
$K$-vector spaces.

**Sign conventions.** The integers $j$ with $\operatorname{gr}^j D_{\mathrm{dR}}(V) \ne 0$ (the jumps of the Hodge
filtration), counted with multiplicity $\dim_K \operatorname{gr}^j D_{\mathrm{dR}}(V)$, are the Hodge–Tate weights
in the convention of Taylor–Yoshida and Barnet-Lamb–Gee–Geraghty–Taylor, in which the cyclotomic character has
weight $-1$: $D_{\mathrm{dR}}(\mathbb{Q}_p(1)) = K t^{-1}$ has its jump at $j = -1$. They are the negatives of the
Hodge–Tate numbers $i$ of Fontaine–Ouyang, for which $\mathbb{Q}_p(1)$ has $h_1 = 1$. When $K$ is a finite extension
of $\mathbb{Q}_p$, for a representation on a $\overline{\mathbb{Q}}_p$-vector space $W$ and an embedding $\tau \colon K \to \overline{\mathbb{Q}}_p$, $\mathrm{HT}_\tau(W)$
contains $j$ with multiplicity $\dim \operatorname{gr}^j (W \otimes_{\tau, K} B_{\mathrm{dR}})^{G_K}$.

## Depends on

- [Admissible representations for a regular ring of periods](admissible-representations.md)
- [Hodge–Tate representations](hodge-tate-representations.md), for $B_{\mathrm{HT}}$ and the comparison of the gradings
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $\chi$ and $C(i)$

## Proof depends on

- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for $B_{\mathrm{dR}}^{G_K} = K$ and $\operatorname{gr}^i D_{\mathrm{dR}}(V) \hookrightarrow (C(i) \otimes V)^{G_K}$
- [Hodge–Tate representations](hodge-tate-representations.md), for de Rham implies Hodge–Tate
- [Structure of the rings of periods](structure-of-the-period-rings.md), for the construction of $\theta$, of $R$ and of $t$ (its item 2)

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  the standing assumption from Chapter 4 on that $K$ is a $p$-adic field with perfect residue field (Preface; §1.1,
  Definition 1.16); Chapter 5, Definition 5.4 and Theorem 5.5 (the ring $R$); §6.2, Proposition 6.11 ($\theta$ surjective),
  Definition 6.13 ($B_{\mathrm{dR}}^+$, $B_{\mathrm{dR}}$), Lemma 6.14, Definition 6.15 (the filtration), Remark 6.16 (the
  two topologies on $B_{\mathrm{dR}}^+$, the canonical one weaker),
  Proposition 6.22 ($t$), Proposition 6.24 ($\operatorname{gr} B_{\mathrm{dR}} = B_{\mathrm{HT}}$), Proposition 6.26
  ($B_{\mathrm{dR}}^{G_K} = K$); §6.3, Definition 6.27 (de Rham), Lemma 6.28, the exact sequences after
  Definition 6.32, Proposition 6.33 (de Rham implies Hodge–Tate) and Theorem 6.34.
- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), arXiv:math/0412357 (version 2), §1, pp. 3–4 (de Rham representations over
  $\overline{\mathbb{Q}}_\ell$ and $\mathrm{HT}_\tau$, containing $j$ with multiplicity
  $\dim \operatorname{gr}^j (V \otimes_{\tau, K} B_{\mathrm{DR}})^{\operatorname{Gal}(K^{ac}/K)}$).
- T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, "Potential automorphy and change of weight", Ann. of
  Math. 179 (2014), arXiv:1010.2561 (version 2), Notation, p. 8 ($\mathrm{HT}_\tau(\epsilon_l) = \{-1\}$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses de Rham representations as `Formalism.MainNotions.N.IsDR` and their weights as
  `GlobalTheory.Pst.IsJumpsAt`.
