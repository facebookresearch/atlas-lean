# Bloch–Kato dimension formula

Let $K$ be a finite extension of $\mathbb{Q}_p$ and $V$ a de Rham $p$-adic representation of $G_K$, with
$D_{\mathrm{dR}}^+(V) = \operatorname{Fil}^0 D_{\mathrm{dR}}(V)$. Then $H^1_f(G_K, V)$ is finite-dimensional and

$$\dim_{\mathbb{Q}_p} H^1_f(G_K, V) = \dim_{\mathbb{Q}_p} \bigl(D_{\mathrm{dR}}(V)/D_{\mathrm{dR}}^+(V)\bigr) + \dim_{\mathbb{Q}_p} H^0(G_K, V),$$

where the first term on the right is $[K : \mathbb{Q}_p]$ times the dimension over $K$. In terms of Hodge–Tate
weights in the convention where the cyclotomic character has weight $-1$ (the jumps $j$ of the filtration on
$D_{\mathrm{dR}}(V)$), the first term is $[K : \mathbb{Q}_p]$ times the number of weights $j < 0$, counted with
multiplicity; if $H^0(G_K, V) = 0$, then $\dim H^1_f(G_K, V)$ is $[K : \mathbb{Q}_p]$ times the number of negative
weights in this convention.

## Depends on

- [Bloch–Kato subgroups of local Galois cohomology](bloch-kato-subgroups.md)
- [de Rham representations](de-rham-representations.md), for $D_{\mathrm{dR}}$ and its filtration

## Proof depends on

- [Fundamental exact sequence of p-adic Hodge theory](fundamental-exact-sequence.md), for the exact sequence $0 \to \mathbb{Q}_p \to B_{\mathrm{cris}} \oplus B_{\mathrm{dR}}^+ \to B_{\mathrm{cris}} \oplus B_{\mathrm{dR}} \to 0$ tensored with $V$
- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for the injectivity of $H^1(G_K, B_{\mathrm{dR}}^+ \otimes V) \to H^1(G_K, B_{\mathrm{dR}} \otimes V)$ (Bellaïche, Lemma 2.6)
- [The long exact sequence of continuous cohomology](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/continuous-cochain-cohomology/long-exact-sequence-for-continuous-cohomology.md), for the long exact sequences of continuous cohomology of the sequences of period rings tensored with $V$, which exist because their maps have continuous set-theoretic sections (Bloch–Kato, Remarks 1.18; NSW (2.7.2))

## Sources

- S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", in *The Grothendieck Festschrift*, vol. I,
  Progr. Math. 86, Birkhäuser, 1990, 333–400, <http://math.stanford.edu/~conrad/BSDseminar/refs/BKTamagawa.pdf>:
  Lemma 3.8.1 and Corollary 3.8.4 (the diagram of exact sequences obtained by tensoring (1.17) with $V$ and taking
  Galois cohomology, and $\dim_{\mathbb{Q}_p} H^1_f(K, V) = \dim_{\mathbb{Q}_p}(DR(V)/DR(V)^0) + \dim_{\mathbb{Q}_p} H^0(K, V)$), p. 355;
  Remarks 1.18 (the continuous sections), p. 341.
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.2.1, Proposition 2.8
  ("Assume that $V$ is de Rham … $\dim_{\mathbb{Q}_p} H^1_f(G_K, V) = \dim_{\mathbb{Q}_p}(D_{\mathrm{dR}}(V)/D^+_{\mathrm{dR}}(V)) +
  \dim_{\mathbb{Q}_p} H^0(G_K, V)$") with its proof and Lemma 2.6, and the remark after Exercise 2.16 (the count of
  negative Hodge–Tate weights; Bellaïche's weights are the jumps of the Hodge filtration, so that his
  Exercise 2.17 has $H^1_f = 0$ when all weights are positive).
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §9.3, Definition 9.23 (the tangent space $t_V$) and Propositions 9.25–9.26.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the formula as the part `DimFormula` of `GlobalTheory.Published.BlochKatoLocal`.
