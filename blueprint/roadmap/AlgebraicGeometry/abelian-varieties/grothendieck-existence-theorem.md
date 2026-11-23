# Grothendieck's existence theorem

Let $A$ be a noetherian adic ring, for instance a complete noetherian local ring, $I$ an ideal of
definition of $A$, $S = \operatorname{Spec} A$, $S_0 = \operatorname{Spec}(A/I)$ and
$\hat S = \operatorname{Spf} A$. For a scheme $X$ over $S$ write $\hat X$ for its formal completion
along $X \times_S S_0$, and $\hat{\mathcal{F}}$ for the completion of a coherent sheaf
$\mathcal{F}$ on $X$.

1. (Existence theorem.) If $X \to S$ is separated and of finite type, then
   $\mathcal{F} \mapsto \hat{\mathcal{F}}$ is an equivalence from the category of coherent
   $\mathcal{O}_X$-modules whose support is proper over $S$ to the category of coherent
   $\mathcal{O}_{\hat X}$-modules whose support is proper over $\hat S$. In particular, if $X$ is
   proper over $S$, completion is an equivalence from coherent $\mathcal{O}_X$-modules to coherent
   $\mathcal{O}_{\hat X}$-modules.
2. (Algebraization of morphisms.) If $X \to S$ is proper and $Y \to S$ is separated and of finite
   type, then $f \mapsto \hat f$ is a bijection
   $\operatorname{Hom}_S(X, Y) \to \operatorname{Hom}_{\hat S}(\hat X, \hat Y)$. Thus completion is
   fully faithful from schemes proper over $S$ to formal schemes proper over $\hat S$.
3. (Algebraization of formal schemes.) Let $\mathfrak{X} \to \hat S$ be a proper morphism of formal
   schemes and $\mathcal{L}$ an invertible $\mathcal{O}_{\mathfrak{X}}$-module whose restriction
   $\mathcal{L}_0 = \mathcal{L} / I \mathcal{L}$ to $X_0 = \mathfrak{X} \times_{\hat S} S_0$ is ample.
   Then $\mathfrak{X}$ is algebraizable: $\mathfrak{X} \cong \hat X$ for a scheme $X$ proper over
   $S$; and for every such $X$ there is an ample $\mathcal{O}_X$-module $\mathcal{M}$ with
   $\hat{\mathcal{M}} \cong \mathcal{L}$, so that $X$ is projective over $S$.

Grothendieck remarks that some formal schemes proper over $\operatorname{Spf} A$ are not
algebraizable, which is why item (3) needs the invertible sheaf. Item (3) is the algebraization step
of [Mumford's construction](mumford-construction-of-degenerating-abelian-varieties.md), and Chai and
Oort use it to algebraize the universal formal deformation of a polarized abelian variety.

## Sources

- A. Grothendieck (with J. Dieudonné), "Éléments de géométrie algébrique III. Étude cohomologique des
  faisceaux cohérents, première partie", Publ. Math. IHÉS 11 (1961), 5–167,
  <http://www.numdam.org/item?id=PMIHES_1961__11__5_0>: §5, Théorème (5.1.4) and Corollaire (5.1.6)
  (existence theorem), Théorème (5.4.1) with the paragraph after its proof (algebraization of
  morphisms; algebraizable formal schemes), Remarque (5.4.3) (non-algebraizable formal schemes) and
  Théorème (5.4.5) (algebraization of a proper formal scheme with an invertible sheaf ample on the
  closed fibre).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.16)
  (3) (the formal polarized abelian scheme of a polarized deformation is algebraizable).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the algebraization of morphisms and of schemes, as
  `GlobalTheory.Published.FormalAlgebraisation`.
