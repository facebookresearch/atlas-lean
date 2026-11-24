# Weakly admissible implies admissible

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$), with maximal absolutely unramified subfield $K_0$. For a
filtered $(\varphi, N)$-module $D$ over $K$ let $V_{\mathrm{st}}(D) = \{ v \in B_{\mathrm{st}} \otimes_{K_0} D :
\varphi v = v, \ N v = 0, \ 1 \otimes v \in \operatorname{Fil}^0 (K \otimes_{K_0} (B_{\mathrm{st}} \otimes_{K_0} D)) \}$,
with $\varphi$ and $N$ acting on the tensor product by $\varphi \otimes \varphi$ and $N \otimes 1 + 1 \otimes N$, the
filtration induced from $B_{\mathrm{dR}} \otimes_K D_K$, and $G_K$ acting on the first factor. Then:

1. if $V$ is a semistable $p$-adic representation of $G_K$, then $D_{\mathrm{st}}(V)$ is weakly admissible and
   $V \cong V_{\mathrm{st}}(D_{\mathrm{st}}(V))$ naturally (Fontaine);
2. if $D$ is weakly admissible, then $V_{\mathrm{st}}(D)$ is a semistable representation with
   $D_{\mathrm{st}}(V_{\mathrm{st}}(D)) \cong D$ (Colmez–Fontaine);
3. hence $D_{\mathrm{st}}$ is an equivalence from semistable $p$-adic representations to weakly admissible
   filtered $(\varphi, N)$-modules over $K$, with quasi-inverse $V_{\mathrm{st}}$, compatible with tensor products and
   duals; it restricts to an equivalence $D_{\mathrm{cris}}$ from crystalline representations to weakly
   admissible filtered $\varphi$-modules ($N = 0$).

## Depends on

- [Semistable and potentially semistable representations](semistable-representations.md), for $B_{\mathrm{st}}$, $D_{\mathrm{st}}$ and semistable representations
- [Weakly admissible filtered (φ, N)-modules](weakly-admissible-filtered-phi-n-modules.md)
- [Crystalline representations](crystalline-representations.md), for the crystalline case

## Proof depends on

- [Structure of the rings of periods](structure-of-the-period-rings.md), for the Dieudonné–Manin classification and the slope filtrations of $\varphi$-modules, the fundamental lemma, the principal ideal domain $B_e$ and the proofs of Chapter 9, §§9.1–9.5 (its items 4–6)
- [Fundamental exact sequence of p-adic Hodge theory](fundamental-exact-sequence.md)
- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for $C(\eta)^{G_K}$ (Fontaine–Ouyang, Corollary 4.45, used in §9.1) and $H^1(G_K, C(i)) = 0$ for $i \ne 0$ (Proposition 4.46, used in the proof of Lemma 9.50), both in the generality of every $p$-adic field

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  the standing assumption from Chapter 4 on that $K$ is a $p$-adic field with perfect residue field (Preface; §1.1,
  Definition 1.16); §8.3.2, Definition 8.52 ($V_{\mathrm{st}}$), Theorem B (1)–(3), Remark 8.53, Proposition B1, Exercise 8.54,
  Proposition B2 and Remark 8.55 (the first proof of Proposition B2 is by P. Colmez and J.-M. Fontaine,
  "Construction des représentations p-adiques semi-stables", Invent. Math. 140 (2000), 1–43); Chapter 9 (the
  proofs).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  develops filtered $\varphi$-modules in `Formalism.WeaklyAdmissibleFiltrations`.
