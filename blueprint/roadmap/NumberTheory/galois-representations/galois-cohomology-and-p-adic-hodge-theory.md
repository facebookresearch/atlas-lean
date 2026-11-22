# Galois cohomology and p-adic Hodge theory

This node covers the Galois cohomology of local and global fields and the theory of $p$-adic
representations of the Galois groups of $p$-adic fields. Let $K$ be a finite extension of
$\mathbb{Q}_p$ with absolute Galois group $G_K$, let $F$ be a number field, and let $S$ be a set
of places of $F$ containing the archimedean ones, with $G_S$ the Galois group of the maximal
extension of $F$ unramified outside $S$. For a finite Galois module $M$ write
$M' = \operatorname{Hom}(M, \mu)$, where $\mu$ is the group of roots of unity of a separable
closure.

- **Local duality.** For a finite $G_K$-module $M$ and $0 \le i \le 2$, the cup product
  $H^i(G_K, M) \times H^{2-i}(G_K, M') \to H^2(G_K, \mu) \cong \mathbb{Q}/\mathbb{Z}$ is a
  perfect pairing of finite groups, and $H^i(G_K, M) = 0$ for $i \ge 3$ (Tate).
- **Local Euler characteristic.** For such $M$,
  $\#H^0(G_K, M) \cdot \#H^2(G_K, M) / \#H^1(G_K, M) = \lVert \#M \rVert_K$, the normalized
  absolute value of $K$ evaluated at the order of $M$ (Tate).
- **Global duality.** For a finite $G_S$-module $M$ whose order is a unit outside $S$: the
  Poitou–Tate exact sequence; for finite $S$, Tate's global Euler characteristic formula; and
  Wiles's formula comparing the orders of the Selmer groups $H^1_{\mathcal{L}}(F, M)$ and
  $H^1_{\mathcal{L}^D}(F, M')$ cut out by a collection $\mathcal{L}$ of local conditions (the
  unramified classes at almost all places) and by its orthogonal collection $\mathcal{L}^D$ under
  local duality.
- **$\ell$-adic representations, $\ell \ne p$.** Grothendieck's $\ell$-adic monodromy theorem:
  for every $\ell$-adic representation of $G_K$ an open subgroup of the inertia group acts
  unipotently. On these representations $V \mapsto (D_\ell(V), N)$ is a fully faithful functor to
  Weil–Deligne representations.
- **Period rings.** Fontaine's rings $B_{\mathrm{HT}}$, $B_{\mathrm{dR}}$ and
  $B_{\mathrm{cris}} \subset B_{\mathrm{st}} \subset B_{\mathrm{dR}}$, and the Hodge–Tate, de Rham,
  semistable and crystalline $p$-adic representations of $G_K$. The functor $D_{\mathrm{st}}$ is
  an equivalence between semistable representations and weakly admissible filtered
  $(\varphi, N)$-modules; that every weakly admissible module comes from a representation is the
  theorem of Colmez and Fontaine. Every de Rham representation is potentially semistable (the
  $p$-adic monodromy theorem: Berger reduced it to Crew's conjecture, proved by André, Mebkhout and
  Kedlaya).
- **Bloch–Kato groups.** The subspaces $H^1_e \subset H^1_f \subset H^1_g$ of
  $H^1(G_K, V)$ for a $p$-adic representation $V$. If $V$ is de Rham, then
  $\dim_{\mathbb{Q}_p} H^1_f(G_K, V) = \dim_{\mathbb{Q}_p} D_{\mathrm{dR}}(V)/D^{+}_{\mathrm{dR}}(V) + \dim_{\mathbb{Q}_p} H^0(G_K, V)$,
  and under local duality the orthogonal of $H^1_f(G_K, V)$ is $H^1_f(G_K, V^*(1))$.
- **Integral comparison.** For a $p$-divisible group $G$ over $\mathcal{O}_C$, where $C$ is an
  algebraically closed complete extension of $\mathbb{Q}_p$, the Hodge–Tate sequence
  $0 \to \operatorname{Lie} G \otimes C(1) \to T_p G \otimes C \to (\operatorname{Lie} G^\vee \otimes C)^\vee \to 0$
  is exact; its integral version over $\mathcal{O}_C$ is exact up to cohomology killed by
  $p^{1/(p-1)+\varepsilon}$ for every $\varepsilon > 0$ (Fargues). For a bounded prism
  $(A, (p))$ and a smooth $p$-adic formal scheme $X$ over $A/p$, there is a canonical
  Frobenius-equivariant isomorphism of commutative algebras in the derived category of $A$-modules
  between crystalline cohomology $R\Gamma_{\mathrm{crys}}(X/A)$ and the derived completed base change
  $R\Gamma_{\Delta}(X/A) \mathbin{\widehat{\otimes}}^{L}_{A, \varphi_A} A$ of prismatic cohomology along
  the Frobenius $\varphi_A$ of $A$, and prismatic $F$-crystals on $\operatorname{Spf}(\mathcal{O}_K)$ are
  equivalent to $\mathbb{Z}_p$-lattices with continuous $G_K$-action in crystalline
  representations (Bhatt–Scholze).

Class field theory, the cohomology of abstract groups and the Galois representations attached to
elliptic curves are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below.

1. Cohomology of profinite groups with coefficients in discrete modules, by continuous cochains, as
   the direct limit of the cohomology of their finite quotients; then local Galois cohomology:
   finiteness and cohomological dimension 2 of $G_K$, local duality, the local Euler characteristic
   formula, and unramified cohomology.
2. Global Galois cohomology: the groups $G_S$, the Poitou–Tate sequence, the global Euler
   characteristic formula, collections of local conditions and Wiles's formula, which use step 1.
3. Weil–Deligne representations and the $\ell$-adic monodromy theorem.
4. The period rings as definition pages, then the classes of representations they define, the
   $D_{\mathrm{st}}$ equivalence, the theorem that weakly admissible modules come from
   representations, and the $p$-adic monodromy theorem.
5. The Bloch–Kato groups, the dimension formula and the orthogonality statement, which use steps 1
   and 4.
6. The Hodge–Tate sequence for $p$-divisible groups, prismatic cohomology with its crystalline
   comparison, and the classification of crystalline lattices by prismatic $F$-crystals.

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren der
  mathematischen Wissenschaften 323, Springer, 2008; electronic edition, version 2.3 (2020),
  <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.1.8) Theorem (cohomological dimension),
  (7.2.6) Theorem (Tate duality), (7.3.1) Theorem (local Euler characteristic), (8.6.10)
  (Poitou–Tate sequence), (8.7.4) (global Euler–Poincaré characteristic), (8.7.8) Definition
  (collections of local conditions) and (8.7.9) Theorem (Wiles's formula).
- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter II, §4: discrete $G$-modules over a
  profinite group, continuous cochains, and Proposition 4.2 (their cohomology is the direct limit of the
  cohomology of the finite quotients $G/H$ with coefficients $M^H$).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., BookSurge, 2006,
  <https://www.jmilne.org/math/Books/ADTnot.pdf>: Chapter I, Corollary 2.3 (local duality),
  Theorem 2.8 (local Euler characteristic), Theorem 4.10 (Poitou–Tate) and Theorem 5.1 (global
  Euler characteristic).
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of
  2022-05-26), archived at
  <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §2.3.1, Theorem 2.26 and Corollary 2.27 (the $\ell$-adic monodromy theorem); §2.3.3,
  Definition 2.33 and Example 2.35 (Weil–Deligne representations); Definitions 6.1, 6.13, 7.7 and 8.1 (the period
  rings; Definition 8.1 defines $B_{\mathrm{st}}$ as the subalgebra $B_{\mathrm{cris}}[u]$ of
  $B_{\mathrm{dR}}$) and 6.3, 6.27 and 8.9 (Hodge–Tate, de Rham, semistable and crystalline
  representations), Definition 8.39 (weakly admissible filtered $(\varphi, N)$-modules, called
  admissible there);
  §8.3, Theorem A with Remark 8.50 (the $p$-adic monodromy theorem), Theorem B, and Proposition B2
  with Remark 8.55 (weakly admissible modules come from representations; first proved by P. Colmez
  and J.-M. Fontaine, Invent. Math. 140 (2000), 1–43).
- L. Berger, "Représentations p-adiques et équations différentielles", Invent. Math. 148 (2002),
  219–284, author's version <https://perso.ens-lyon.fr/laurent.berger/articles/article02.pdf>:
  Théorème 0.7 (de Rham representations are potentially semistable).
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, lectures at the Clay
  Mathematics Institute summer school, Honolulu, 2009,
  <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.2, Definition 2.5
  ($H^1_f$), Proposition 2.8 (dimension formula) and Theorem 2.1 (orthogonality), and §2.2.2 (the
  variants $H^1_g$ and $H^1_e$, and $H^1_e \subset H^1_f \subset H^1_g$). The groups are those of
  S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", The Grothendieck
  Festschrift I, Progr. Math. 86, Birkhäuser, 1990, 333–400.
- P. Scholze and J. Weinstein, "Moduli of p-divisible groups", Cambridge J. Math. 1 (2013),
  145–237, arXiv:1211.6357 (version 2): Proposition 4.3.6 and Remark 4.3.7 (the integral
  Hodge–Tate sequence, after Fargues), Proposition 5.1.6 (the Hodge–Tate sequence over $C$).
- B. Bhatt and P. Scholze, "Prisms and prismatic cohomology", arXiv:1905.08229 (version 4):
  Theorem 1.8 (1) (crystalline comparison, through the derived completed Frobenius base change).
- B. Bhatt and P. Scholze, "Prismatic F-crystals and crystalline Galois representations",
  Cambridge J. Math. 11 (2023), 507–562, arXiv:2106.14735 (version 2): Theorem 1.2.
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  Related formal statements in Alpöge's proof, often in specialised forms,
  include `Formalism.GaloisCohomology.LocalTateDualityK`,
  `GlobalTheory.Published.PoitouTateNormalised` (the nine-term sequence for finite sets of places,
  assuming $\ell \ne 2$ or $F$ totally complex), `ReciprocityTheory.Gal.GreenbergWiles`,
  `GlobalTheory.Published.FontaineBcris`, `GlobalTheory.Published.DeRhamPotSemistable`,
  `GlobalTheory.Published.BlochKatoLocal`, `GlobalTheory.Published.BhattScholzeCrystallineLattices`
  and `GlobalTheory.CompanionTheory.Ar.HT.FarguesExact` (a kernel–annihilator identity for the
  Hodge–Tate map of a $p$-divisible group).
