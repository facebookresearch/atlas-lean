# Bloch–Kato orthogonality

Let $K$ be a finite extension of $\mathbb{Q}_p$ and $V$ a de Rham $p$-adic representation of $G_K$, with
$V^*(1)$ its twisted dual. Under the perfect pairing

$$H^1(G_K, V) \times H^1(G_K, V^*(1)) \xrightarrow{\ \cup\ } H^2(G_K, \mathbb{Q}_p(1)) \cong \mathbb{Q}_p$$

of local duality, the orthogonal complement of $H^1_f(G_K, V)$ is $H^1_f(G_K, V^*(1))$. Moreover the orthogonal
complement of $H^1_e(G_K, V)$ is $H^1_g(G_K, V^*(1))$, and that of $H^1_g(G_K, V)$ is $H^1_e(G_K, V^*(1))$.

## Depends on

- [Bloch–Kato subgroups of local Galois cohomology](bloch-kato-subgroups.md)
- [Galois cohomology of ℓ-adic representations of a p-adic field](../galois-cohomology-of-local-fields/galois-cohomology-of-l-adic-representations.md), for the duality pairing with $p$-adic coefficients
- [de Rham representations](de-rham-representations.md)

## Proof depends on

- [Bloch–Kato dimension formula](bloch-kato-dimension-formula.md), applied to $V$ and $V^*(1)$
- [de Rham representations](de-rham-representations.md), for $\dim_K D_{\mathrm{dR}}^+(V) + \dim_K D_{\mathrm{dR}}^+(V^*(1)) = \dim_{\mathbb{Q}_p} V$
- [Galois cohomology of ℓ-adic representations of a p-adic field](../galois-cohomology-of-local-fields/galois-cohomology-of-l-adic-representations.md), for the Euler characteristic formula and duality
- [Fundamental exact sequence of p-adic Hodge theory](fundamental-exact-sequence.md), for the compatibility of cup products with its connecting maps, which makes $H^1_f(G_K, V)$ and $H^1_f(G_K, V^*(1))$ orthogonal, and for the sequence $0 \to \mathbb{Q}_p \to B_e \oplus B_{\mathrm{dR}}^+ \to B_{\mathrm{dR}} \to 0$, whose connecting maps give the $e$/$g$ statement (Bloch–Kato (3.8.6)–(3.8.7))
- [Tate–Sen theorem on the Galois cohomology of C(i)](tate-sen-theorem.md), for the cohomology of $C(j)$, which reduces the $e$/$g$ statement to the perfectness of $H^1(K, C \otimes V) \times H^0(K, C \otimes V^*) \to H^2(K, \mathbb{Q}_p(1))$ and to the case $V = \mathbb{Q}_p$ (Bloch–Kato (3.8.8))
- [Hodge–Tate representations](hodge-tate-representations.md), for the Hodge–Tate decomposition of the de Rham representation $V$ used in that reduction
- [Galois cohomology of roots of unity over a p-adic field](../galois-cohomology-of-local-fields/cohomology-of-roots-of-unity-over-p-adic-fields.md), for the Kummer identification $H^1(K, \mathbb{Q}_p(1)) \cong (\varprojlim_n K^\times/K^{\times p^n}) \otimes \mathbb{Q}$, under which the boundary $K \to H^1(K, \mathbb{Q}_p(1))$ of the last step is the $p$-adic exponential (Bloch–Kato, p. 358)
- [The p-adic exponential on a neighbourhood of zero](../../../p-adic-numbers/p-adic-exponential.md), for that exponential
- [The long exact sequence of continuous cohomology](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/continuous-cochain-cohomology/long-exact-sequence-for-continuous-cohomology.md), for the long exact sequences of continuous cohomology with period-ring coefficients, which exist because the maps of the fundamental exact sequences have continuous sections (Bloch–Kato, Remarks 1.18)

## Sources

- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.2.1, Theorem 2.1 (Bloch
  and Kato: for de Rham $V$ the orthogonal of $H^1_f(G_K, V)$ is $H^1_f(G_K, V^*(1))$) with its proof and
  Exercise 2.16; §2.2.2, Proposition 2.11 (the orthogonal of $H^1_e$ is $H^1_g$ of the dual, for de Rham $V$).
- S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", in *The Grothendieck Festschrift*, vol. I,
  Progr. Math. 86, Birkhäuser, 1990, 333–400, <http://math.stanford.edu/~conrad/BSDseminar/refs/BKTamagawa.pdf>:
  Proposition 3.8 and its proof: the $f$/$f$ statement through (3.8.5) and the dimension formula (3.8.4), and the
  $e$/$g$ statement through the diagrams (3.8.6)–(3.8.7), the pairing (3.8.8), Tate's computation of $H^i(K, C_p(j))$,
  the Hodge–Tate decomposition and the identification of the boundary map with the $p$-adic exponential, pp. 356–359;
  Remarks 1.18 (long exact sequences of continuous cohomology for the sequences (1.17)).
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §9.3, Theorem 9.27 (the three orthogonality relations for semistable $V$, citing Bloch–Kato,
  Proposition 3.8).
- S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", The Grothendieck Festschrift I,
  Progr. Math. 86, Birkhäuser, 1990, 333–400: Proposition 3.8, as cited by Fontaine–Ouyang.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the orthogonality of the $H^1_f$, for a de Rham representation and a dual one, as the part
  `RationalDuality` of `GlobalTheory.Published.BlochKatoLocal`.
