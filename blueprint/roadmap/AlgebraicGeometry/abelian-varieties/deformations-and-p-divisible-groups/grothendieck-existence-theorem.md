# Grothendieck's existence theorem

This node is still to be broken down: the statements are precise, but their proofs are not.

Let $A$ be a noetherian adic ring, for instance a complete noetherian local ring, $I$ an ideal of
definition of $A$, $S = \operatorname{Spec} A$, $S_0 = \operatorname{Spec}(A/I)$ and $\hat S =
\operatorname{Spf} A$. For a scheme $X$ over $S$ write $\hat X$ for its formal completion along $X
\times_S S_0$, and $\hat{\mathcal{F}}$ for the completion of a coherent sheaf $\mathcal{F}$ on $X$.

1. (Existence theorem.) If $X \to S$ is separated and of finite type, then $\mathcal{F} \mapsto
   \hat{\mathcal{F}}$ is an equivalence from the category of coherent $\mathcal{O}_X$-modules whose
   support is proper over $S$ to the category of coherent $\mathcal{O}_{\hat X}$-modules whose
   support is proper over $\hat S$. In particular, if $X$ is proper over $S$, completion is an
   equivalence from coherent $\mathcal{O}_X$-modules to coherent $\mathcal{O}_{\hat X}$-modules.
2. (Algebraization of morphisms.) If $X \to S$ is proper and $Y \to S$ is separated and of finite
   type, then $f \mapsto \hat f$ is a bijection $\operatorname{Hom}_S(X, Y) \to
   \operatorname{Hom}_{\hat S}(\hat X, \hat Y)$. Thus completion is fully faithful from schemes
   proper over $S$ to formal schemes proper over $\hat S$.
3. (Algebraization of formal schemes.) Let $\mathfrak{X} \to \hat S$ be a proper morphism of formal
   schemes and $\mathcal{L}$ an invertible $\mathcal{O}_{\mathfrak{X}}$-module whose restriction
   $\mathcal{L}_0 = \mathcal{L} / I \mathcal{L}$ to $X_0 = \mathfrak{X} \times_{\hat S} S_0$ is
   ample. Then $\mathfrak{X}$ is algebraizable: $\mathfrak{X} \cong \hat X$ for a scheme $X$ proper
   over $S$; and for every such $X$ there is an ample $\mathcal{O}_X$-module $\mathcal{M}$ with
   $\hat{\mathcal{M}} \cong \mathcal{L}$, so that $X$ is projective over $S$.

Grothendieck remarks that some formal schemes proper over $\operatorname{Spf} A$ are not
algebraizable, which is why item (3) needs the invertible sheaf. Through the dictionary between
formal schemes and adic systems (Scholies (5.1.7) and (5.4.2)), items (1)–(3) say the same of
compatible systems of coherent sheaves, of morphisms and of proper schemes $X_n$ over the
$A/I^{n+1}$ with compatible line bundles ample on $X_0$. Item (3) is the algebraization step of
[Mumford's construction](../moduli-and-compactifications/mumford-construction-of-degenerating-abelian-varieties.md), and Chai and
Oort use it to algebraize the universal formal deformation of a polarized abelian variety; without a
polarization a proper formal abelian scheme need not be algebraizable, and to algebraize a formal
abelian scheme one also algebraizes its group law, by item (2), and checks separately that the
algebraized scheme is flat and smooth with abelian fibres: item (2) algebraizes morphisms and
identities between them, and does not by itself give smoothness.

## Depends on

- [Adically complete modules](../../../RingTheory/local-rings/adic-completion/adically-complete-module.md),
  for the noetherian adic ring $A$ of the statement, which is $I$-adically complete for an ideal of
  definition $I$

## Proof depends on

- [Standard results of coherent cohomology on projective varieties](../../birational-geometry/standard-results-of-coherent-cohomology.md),
  for the finiteness theorem, on which the comparison theorem for the cohomology of completions
  rests

## Expansion

A good expansion has pages for: the comparison theorem for the cohomology of the completion of a
coherent sheaf (EGA III, §4); the existence theorem for projective morphisms (§5.2); the lemmas
(5.3.1)–(5.3.4) and the end of the proof (5.3.5), through Chow's lemma and noetherian induction;
Corollary (5.1.8) on closed subschemes, from which Theorem (5.4.1) follows by algebraizing the graph
of a formal morphism; and Theorem (5.4.5), proved by embedding $\mathfrak{X}$ in a projective space
by lifted sections of a power of $\mathcal{L}$ and algebraizing the coherent ideal of its image.

A good expansion also states and links:

- formal schemes, formal completions and coherent sheaves on them (EGA I, chapter 0, §7, and chapter
  I, §10), and the adic thickenings $X \times_S \operatorname{Spec}(A / I^{n+1})$ (stated in the
  project as `AlgebraicGeometry.adicThickening`,
  MathlibExt/AlgebraicGeometry/AdicThickening.lean:61–63), for the statement

## Sources

- A. Grothendieck and J. Dieudonné, "Éléments de géométrie algébrique I. Le langage des schémas",
  Publ. Math. IHÉS 4 (1960), 5–228, <http://www.numdam.org/item?id=PMIHES_1960__4__5_0>: chapter 0,
  §7 (adic rings), and chapter I, §10 (formal schemes).
- A. Grothendieck (with J. Dieudonné), "Éléments de géométrie algébrique III. Étude cohomologique
  des faisceaux cohérents, première partie", Publ. Math. IHÉS 11 (1961), 5–167,
  <http://www.numdam.org/item?id=PMIHES_1961__11__5_0>: §5, Théorème (5.1.4) and Corollaire (5.1.6)
  (existence theorem), Scholie (5.1.7), Corollaire (5.1.8), §5.3 with 5.3.5 (end of the proof of the
  existence theorem), Théorème (5.4.1) with the paragraph after its proof (algebraization of
  morphisms; algebraizable formal schemes), Scholie (5.4.2), Remarque (5.4.3) (non-algebraizable
  formal schemes) and Théorème (5.4.5) with its proof (algebraization of a proper formal scheme with
  an invertible sheaf ample on the closed fibre).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.16)
  (2)–(3) (universal deformations of an abelian variety and of a polarized one; the formal polarized
  abelian scheme of a polarized deformation is algebraizable).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states items (2) and (3) in the form of compatible systems over the $A/I^{e+1}$, as
  `GlobalTheory.Published.FormalAlgebraisation`.
