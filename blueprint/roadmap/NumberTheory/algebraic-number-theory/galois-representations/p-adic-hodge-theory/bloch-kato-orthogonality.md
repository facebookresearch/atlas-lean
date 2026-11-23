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
- [Fundamental exact sequence of p-adic Hodge theory](fundamental-exact-sequence.md), for the compatibility of cup products with its connecting maps, which makes $H^1_f(G_K, V)$ and $H^1_f(G_K, V^*(1))$ orthogonal

## Sources

- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.2.1, Theorem 2.1 (Bloch
  and Kato: for de Rham $V$ the orthogonal of $H^1_f(G_K, V)$ is $H^1_f(G_K, V^*(1))$) with its proof and
  Exercise 2.16; §2.2.2, Proposition 2.11 (the orthogonal of $H^1_e$ is $H^1_g$ of the dual, for de Rham $V$).
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
