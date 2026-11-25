# Semistable reduction theorem for abelian varieties

A **semi-abelian variety** over a field $k$ is a smooth connected commutative group scheme $G$ of
finite type over $k$ such that $G_{\bar k}$, for an algebraic closure $\bar k$, is an extension of an
abelian variety by a torus; the extension then descends to $k$: there is a unique exact sequence
$1 \to T \to G \to B \to 1$ with $T$ a $k$-torus and $B$ an abelian variety over $k$.

Let $R$ be a discrete valuation ring with fraction field $K$ and residue field $k$. An
[abelian variety](abelian-scheme.md) $A$ over $K$ has **semistable reduction** over $R$ if the
identity component $(\mathcal{A}_k)^0$ of the special fibre of its [Néron model](neron-model.md)
$\mathcal{A}$ is a semi-abelian variety over $k$. For a semi-local Dedekind domain $R'$ with fraction
field $K'$, an abelian variety over $K'$ has semistable reduction over $R'$ if it has semistable
reduction over the localization of $R'$ at each maximal ideal.

**Theorem** (Grothendieck). For every abelian variety $A$ over $K$ there is a finite separable
extension $K'/K$ such that $A_{K'}$ has semistable reduction over the integral closure $R'$ of $R$
in $K'$.

Since $K'/K$ is separable, $R'$ is a finite $R$-module and a semi-local Dedekind domain, which may have
several maximal ideals; it is local when $R$ is henselian, for instance complete. When $A$ has
semistable reduction over $R$, the relative identity component $\mathcal{A}^0$ of its Néron model, the
complement of the non-identity components of the special fibre, is a semi-abelian scheme over $R$ with
generic fibre $A$, and it commutes with finite extensions, possibly ramified: for a finite extension
$K_1/K$ and a discrete valuation ring $R_1$ of $K_1$ dominating $R$, $(\mathcal{A}^0)_{R_1}$ is the
identity component of the Néron model of $A_{K_1}$ (Conrad, Theorem 4.4 and Corollary 4.5); the full
Néron model, whose component group may grow, need not commute with such extensions. Conrad proves the theorem by reducing it to Jacobians of
smooth proper geometrically connected curves, and deduces the case of Jacobians from the semistable
reduction theorem for curves and Raynaud's description of the Néron model of a Jacobian.

## Depends on

- [Néron model of an abelian variety](neron-model.md)
- [Abelian scheme](abelian-scheme.md), for abelian varieties

## Proof depends on

- [Néron model of an abelian variety](neron-model.md), for the existence of Néron models, their base
  change properties, the reduction to Jacobians, the semistable reduction theorem for curves and
  Raynaud's description of the Néron model of a Jacobian

## Sources

- B. Conrad, "Semistable reduction for abelian varieties", seminar notes, Stanford, 2011,
  <http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf>: §3, the definition of semi-abelian
  varieties and Theorem 3.1 (descent of the torus); §4, the definition of semistable reduction over a
  discrete valuation ring and over a semi-local Dedekind ring, Theorem 4.2 (semistable reduction after
  a finite separable extension, over the integral closure; the integral closure "of $R$ in $K$" there
  is a misprint for $K'$), the remarks after it, Proposition 4.3, Theorem 4.4 and Corollary 4.5 with
  the discussion after it; §7, Theorem 7.13 and Proposition 7.14.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 17.2 and Theorem 17.3
  (statement: an abelian variety acquires semistable reduction after a finite extension).
- A. Grothendieck, "Modèles de Néron et monodromie", Exposé IX in *Groupes de monodromie en géométrie
  algébrique* (SGA 7 I), Lecture Notes in Mathematics 288, Springer, 1972, 313–523.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the case of finite extensions of $\mathbb{Q}_p$, phrased with a
  semi-abelian group scheme over the integral closure of $\mathbb{Z}_p$ in a finite extension whose
  generic fibre is the given abelian variety, as `GlobalTheory.Published.SemistableReductionSt`.
