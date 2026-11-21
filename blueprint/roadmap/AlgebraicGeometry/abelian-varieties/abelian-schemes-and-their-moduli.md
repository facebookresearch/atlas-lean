# Abelian schemes and their moduli

This node covers abelian varieties over fields and abelian schemes over general bases, together with
the reduction, deformation and moduli theory that the arithmetic of abelian varieties uses. An
abelian scheme over a scheme $S$ is a proper smooth group scheme over $S$ whose fibres are abelian
varieties; over a variety $S$ this is a family of abelian varieties.

- **Rigidity.** Abelian varieties are commutative and projective. Rigidity lemma: let $S$ be a
  connected variety, $\pi \colon V \to S$ a proper flat morphism whose fibres are geometrically
  connected varieties, and $\alpha \colon V \to V'$ a morphism to a variety $V'$ over $S$; if
  $\alpha$ maps one fibre $V_s$ to a point, then $\alpha$ factors through $\pi$. Consequently a
  morphism of families of abelian varieties that carries the zero section to the zero section is a
  homomorphism, the group law is determined by the zero section, and families of abelian varieties
  are commutative.
- **Duality and polarizations.** The dual abelian variety $A^\vee$, with its Poincaré sheaf,
  parametrizes the line bundles in $\operatorname{Pic}^0(A)$, so that
  $A^\vee(k) = \operatorname{Pic}^0(A)$, and $A^{\vee\vee} \cong A$. A polarization is an isogeny
  $\lambda \colon A \to A^\vee$ that becomes $\varphi_L$ for an ample line bundle $L$ over an algebraic
  closure (for an abelian scheme: on every geometric fibre); it is principal if it is an isomorphism.
  Zarhin's trick: for every abelian variety $A$, the abelian variety $(A \times A^\vee)^4$ has a
  principal polarization.
- **Néron models and semistable reduction.** Let $R$ be a discrete valuation ring with fraction
  field $K$. For an abelian variety $A$ over $K$ the functor
  $S \mapsto \operatorname{Hom}_K(S \times_R K, A)$ on smooth $R$-schemes is represented by a smooth
  group scheme over $R$, the Néron model (Néron). There is a finite separable extension $K'/K$ such
  that $A_{K'}$ has semistable reduction: the identity component of the special fibre of its Néron
  model is an extension of an abelian variety by a torus (Grothendieck).
- **Complex multiplication.** An abelian variety over $\mathbb{C}$ with complex multiplication has a
  model over a number field that, after a finite extension of that field, has good reduction at every
  prime (Serre–Tate).
- **Deformations.** Serre–Tate: let $S$ be a scheme on which $p$ is locally nilpotent and $S_0$ the
  closed subscheme defined by a locally nilpotent ideal; then abelian schemes over $S$ are
  equivalent to triples $(A_0, X, \varepsilon)$ of an abelian scheme $A_0$ over $S_0$, a
  $p$-divisible group $X$ over $S$ and an isomorphism
  $\varepsilon \colon X \times_S S_0 \to A_0[p^\infty]$. Grothendieck–Messing: a $p$-divisible group
  $X_0$ over a ring $R_0$ has a Dieudonné crystal $\mathbb{D}(X_0)$; over a locally nilpotent
  divided-power extension $R \to R_0$, lifts of $X_0$ to $R$ are equivalent to lifts to
  $\mathbb{D}(X_0)_R$ of its Hodge filtration, and for an abelian scheme $A$ over $R$ the value
  $\mathbb{D}(X_0)_R$ is the first de Rham homology of $A$, with the Hodge filtration.
- **Algebraization.** Let $A$ be a noetherian adic ring, for instance a complete noetherian local
  ring, and $X$ a proper scheme over $\operatorname{Spec} A$. Completion along the closed fibre is
  an equivalence between coherent sheaves on $X$ and on its formal completion, morphisms between such
  schemes algebraize, and a proper formal scheme over $\operatorname{Spf} A$ with an invertible sheaf
  ample on the closed fibre is the completion of a projective $A$-scheme (Grothendieck's existence
  theorem). In particular a formal abelian scheme with such a line bundle comes from an abelian
  scheme.
- **Moduli and degenerations.** The node includes the moduli of principally polarized abelian
  varieties with its toroidal compactifications and its minimal compactification, which Faltings
  and Chai construct from the degenerations of polarized abelian varieties into semi-abelian
  schemes. A semi-abelian scheme is a smooth commutative group scheme whose fibres are extensions of
  abelian varieties by tori. Over a base $\operatorname{Spec} A$ with $A$ an excellent integrally
  closed noetherian ring complete for an $I$-adic topology, Mumford constructs semi-abelian group
  schemes with abelian generic fibre whose fibre over $\operatorname{Spec}(A/I)$ is a split torus,
  as quotients of a split torus by a lattice of periods.

Jacobians of curves and elliptic curves are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below.

1. Abelian varieties over a field: rigidity, commutativity, projectivity, the dual abelian variety
   and biduality, polarizations and Zarhin's trick. The dimension-one and Jacobian cases are under
   [Elliptic curves](../elliptic-curves/README.md) and
   [Algebraic curves](../algebraic-curves/README.md).
2. Abelian schemes: rigidity in families, dual abelian schemes, isogenies and polarizations.
3. Néron models, semistable reduction, and good reduction of abelian varieties with complex
   multiplication.
4. $p$-divisible groups, the Serre–Tate theorem, Dieudonné crystals and Grothendieck–Messing theory,
   and Grothendieck's existence theorem with the algebraization of formal abelian schemes.
5. Moduli of polarized abelian varieties with level structure, semi-abelian degenerations, and the
   toroidal and minimal compactifications.

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Theorem 1.1 and Corollary 1.4
  (rigidity, commutativity), Theorem 6.4 (projectivity), §8 with Theorem 8.9 (dual abelian variety,
  biduality), §11 (polarizations), Theorem 13.12 (Zarhin's trick), Proposition 16.1 and Corollary
  16.2 (rigidity in families), §17 with Remark 17.2 and Theorem 17.3 (Néron models, semistable
  reduction); Chapter II, Proposition 2.10 (good reduction of abelian varieties with complex
  multiplication, due to J.-P. Serre and J. Tate, "Good reduction of abelian varieties", Ann. of
  Math. (2) 88 (1968), 492–517).
- Yu. G. Zarhin, "Abelian varieties over fields of finite characteristic", Open Math. 12 (2014),
  659–674, arXiv:1301.5594 (version 4): §3, proof of Theorem 3.1 (Zarhin's trick, with references
  to Zarhin, Math. Notes 21 (1977), and Invent. Math. 79 (1985)).
- B. Conrad, "Semistable reduction for abelian varieties", seminar notes, Stanford, 2011,
  <http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf>: §4, Theorem 4.2 (semistable reduction
  after a finite separable extension).
- S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, Ergebnisse der Mathematik (3) 21,
  Springer, 1990: the chapters "What Is a Néron Model?" (pp. 6–30) and "Properties of Néron
  Models" (pp. 172–198).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): §2,
  Theorem 2.4 (Grothendieck–Messing) and Theorem 2.7 (Serre–Tate); (10.12) (abelian schemes, duals,
  isogenies, polarizations). Both theorems are proved in W. Messing, *The Crystals Associated to
  Barsotti–Tate Groups: with Applications to Abelian Schemes*, LNM 264, Springer, 1972, chapter
  "The deformation theory and applications" (pp. 150–174).
- A. Grothendieck, "Éléments de géométrie algébrique III. Étude cohomologique des faisceaux
  cohérents, première partie", Publ. Math. IHÉS 11 (1961), 5–167,
  <http://www.numdam.org/item?id=PMIHES_1961__11__5_0>: §5, Théorème (5.1.4) and Corollaire
  (5.1.6) (existence theorem), Théorème (5.4.1) (algebraization of morphisms), Théorème (5.4.5)
  (algebraization of proper formal schemes with an invertible sheaf ample on the closed fibre).
- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Ergebnisse der Mathematik (3)
  22, Springer, 1990: the chapters "Degeneration of Polarized Abelian Varieties" (pp. 31–52),
  "Mumford's Construction" (pp. 53–92), "Toroidal Compactification of A_g" (pp. 93–135) and
  "Modular Forms and the Minimal Compactification" (pp. 136–193).
- D. Mumford, "An analytic construction of degenerating abelian varieties over complete rings",
  Compositio Math. 24 (1972), 239–272, <http://www.numdam.org/item?id=CM_1972__24_3_239_0>: the
  introduction and §4.
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  The library has no licence, so none of its Lean comes into ATLAS; ATLAS has no Lean proof of
  its own. Alpöge's proof uses results of this cluster,
  such as `GlobalTheory.Published.DualAbelianScheme`,
  `GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement` (a polarized-retract statement for abelian
  schemes), `GlobalTheory.Published.SemistableReductionSt`,
  `GlobalTheory.Published.GrothendieckMessing`, `GlobalTheory.Published.FormalAlgebraisation`,
  `GlobalTheory.Published.ToroidalCompactification` and
  `GlobalTheory.Published.principalPolarisationOneSection`.
