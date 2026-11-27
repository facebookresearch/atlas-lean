# Semistable reduction theorem for abelian varieties

This node is still to be broken down: its statement is precise, but its proof is not.

Let $k$ be a field with algebraic closure $\bar k$. The [split torus](split-torus.md) of rank $r$
over $k$ is $\mathbb{G}_m^r = \operatorname{Spec} k[\mathbb{Z}^r]$, with the group law of the Hopf
algebra $k[\mathbb{Z}^r]$. A [torus](is-torus.md) over $k$ is a group scheme $T$ over $k$ whose base
change $T_{\bar k}$ is isomorphic, as a group scheme, to a split torus over $\bar k$; it is affine,
since affineness descends along $\operatorname{Spec} \bar k \to \operatorname{Spec} k$. A group scheme
$G$ over $k$ is an [extension of an abelian variety by a torus](is-extension-of-abelian-variety-by-torus.md)
if there are a torus $T$, an abelian variety $B$ over $k$ (an
[abelian scheme](../../not-yet-classified/abelian-schemes/abelian-scheme.md) over $\operatorname{Spec} k$)
and homomorphisms $T \to G \to B$ such that $G \to B$ is flat and surjective and $T$ is its kernel,
the fibre of $G \to B$ over the zero section of $B$. A homomorphism $G^0 \to G$ is the
[identity component](is-identity-component.md) of $G$ if it is an open immersion whose image is the
connected component of the identity point of $G$.

Let $R$ be a discrete valuation ring with fraction field $K$ and residue field $k$, and let $X$ be an
abelian variety over $K$. A Néron model of $X$ is a smooth separated $R$-scheme $\mathcal{X}$ of
[finite type](../../not-yet-classified/neron-models/finite-type-neron-model.md), with generic fibre
identified with $X$, such that every morphism from the generic fibre of a smooth $R$-scheme $Y$ to $X$
extends uniquely to an $R$-morphism $Y \to \mathcal{X}$; it carries a
[commutative group law](../../not-yet-classified/neron-models/group-structure.md) extending that of
$X$. The abelian variety $X$ has [semistable reduction](has-semistable-reduction.md) at $R$ if it has
a Néron model $\mathcal{X}$, with such a group law, such that the identity component $X_v^0$ of the
special fibre $X_v = \mathcal{X} \otimes_R k$ is an extension of an abelian variety by a torus. Néron
models and their group laws are unique up to unique isomorphism, so this does not depend on the
choice. For a discrete valuation $v$ on a field, semistable reduction at $v$ means semistable reduction
at its valuation ring.

**Theorem** (Grothendieck). Let $X$ be an abelian variety over a field $F$ and $v$ a discrete
valuation on $F$. Then there is a finite Galois extension $L$ of $F$ such that $X_L$ has semistable
reduction at the extensions of $v$ to $L$.

Silverberg and Zarhin print the conclusion as "$X$ has semistable reduction at the extensions of $v$
to $L$", with $X$ over $L$, that is $X_L$. If $\mathcal{O}$ is the valuation ring of $v$, the extensions
of $v$ to $L$ correspond to the valuation rings $w$ of $L$ with $w \cap F = \mathcal{O}$; these are the
localizations of the integral closure of $\mathcal{O}$ in $L$ at its maximal ideals, and they are
discrete valuation rings.

Conrad states the theorem, for an abelian variety $A$ over $K$, with a finite separable extension
$K'/K$ such that $A_{K'}$ has semistable
reduction over the integral closure $R'$ of $R$ in $K'$, that is, at the localization of $R'$ at each
of its maximal ideals. The two forms are the same theorem. A finite Galois extension is separable.
Conversely, let $L$ be a Galois closure of $K'$: every extension of $v$ to $L$ lies over an extension
of $v$ to $K'$, and semistable reduction persists under such an extension of discrete valuation
rings, since the identity component of the Néron model then commutes with base change (Conrad,
Corollary 4.5) and an extension of an abelian variety by a torus stays one after extending the
residue field. Conrad's Proposition 6.5 gives such a Galois extension directly: for $N \ge 3$ prime to
the residue characteristic, $A$ acquires semistable reduction at every place of $K(A[N])$ lying above
$v$. Conrad
calls a smooth connected commutative $k$-group semi-abelian when its base change to $\bar k$ is an
extension of an abelian variety by a torus, and says that $A$ has semistable reduction when
$(\mathcal{A}_k)^0$ is semi-abelian; by his Theorem 3.1 the torus and the extension then descend to
$k$, which is the form above.

Conrad proves the theorem by reducing it to Jacobians of smooth proper geometrically connected
curves, and deduces the case of Jacobians from the semistable reduction theorem for curves and
Raynaud's description of the identity component of the Néron model of a Jacobian.

## Depends on

- [Semistable reduction of an abelian variety](has-semistable-reduction.md)
- [Abelian scheme](../../not-yet-classified/abelian-schemes/abelian-scheme.md), for abelian varieties
  over $F$
- [Base change of an abelian scheme](../../not-yet-classified/abelian-schemes/base-change.md), for
  $X_L$

## Proof depends on

- [Néron model of an abelian variety](../neron-model.md), for the existence of the Néron model of an
  abelian variety, with its group law
- [Abelian varieties are projective](../abelian-varieties-are-projective.md), for the projective
  embedding of $A$ through which Conrad presents it as a quotient of a Jacobian (proof of
  Proposition 4.3)
- [Representability of relative Picard functors](../representability-of-picard-functors.md), for the
  relative Picard functor of a proper flat curve over $R$ as an algebraic space (its target 1;
  Conrad, Theorem 7.12)

## Expansion

A good expansion states and links the following steps of Conrad's proof, which the
[Néron model](../neron-model.md) node's expansion also plans:

- the invariance of semistable reduction under isogenies (Proposition 4.1) and under products;
- the reduction to Jacobians: Bertini slicing, for a smooth proper geometrically connected curve over
  $K$ with a surjection from its Jacobian onto $A$, and Poincaré's reducibility theorem, for an abelian
  variety $B$ with $A \times B$ isogenous to that Jacobian (Proposition 4.3);
- the semistable reduction theorem for curves;
- Raynaud's theorem that $\operatorname{Pic}^0_{X/S}$ of a regular proper flat semistable curve over
  $R$ with smooth generic fibre is a separated scheme (Theorem 7.13), the semi-abelian Picard variety
  of a proper geometrically connected semistable curve over a field (Proposition 7.14), and the open
  immersion criterion of Theorem 4.4, which makes $\operatorname{Pic}^0_{X/S}$ the identity component
  of the Néron model of its generic fibre;
- the base change of the identity component of the Néron model in the semistable case
  (Corollary 4.5), for the passage to a Galois closure;
- the descent of the torus and the extension from $\bar k$ to $k$ (Theorem 3.1), between Conrad's
  semi-abelian varieties and the extensions above.

## Sources

- A. Silverberg and Yu. G. Zarhin, "Semistable reduction and torsion subgroups of abelian
  varieties", *Ann. Inst. Fourier* 45 (1995), 403–420, <https://doi.org/10.5802/aif.1459>: §3,
  pp. 404–405, the Néron model and Definition 3.1 (ii) (semistable reduction: $X_v^0$ is an extension
  of an abelian variety by an affine torus); Theorem 3.4, pp. 405–406 (the theorem as stated here),
  whose proof they cite as Proposition 3.6 of SGA 7 I, Exp. IX.
- A. Grothendieck, "Modèles de Néron et monodromie", Exposé IX in *Groupes de monodromie en géométrie
  algébrique* (SGA 7 I), Lecture Notes in Mathematics 288, Springer, 1972, 313–523: Théorème 3.6,
  which Silverberg and Zarhin cite as Proposition 3.6 (p. 406).
- B. Conrad, "Semistable reduction for abelian varieties", seminar notes, Stanford, 2011,
  <http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf>: §2, Definition 2.10 (tori); §3, the
  definition of semi-abelian varieties and Theorem 3.1 (descent of the torus); §4, the definition of
  semistable reduction over a discrete valuation ring and over a semi-local Dedekind ring,
  Theorem 4.2 (semistable reduction after a finite separable extension, over the integral closure;
  the integral closure "of $R$ in $K$" there is a misprint for $K'$), the remarks after it,
  Propositions 4.1 and 4.3, Theorem 4.4 and Corollary 4.5 with the discussion after it; §6,
  Proposition 6.5; §7, Theorems 7.12 and 7.13 and Proposition 7.14.
- B. Conrad, "Néron models, Tamagawa factors, and Tate-Shafarevich groups", seminar notes taken by
  T. Feng, Stanford, 2015, <https://math.stanford.edu/~conrad/BSDseminar/Notes/L3.pdf>: Theorem 1.1
  (Néron's existence theorem: a smooth separated $R$-scheme of finite type), Example 1.2 and
  Remark 1.3, pp. 2–3 (uniqueness, and finite type is not a formal consequence of the mapping
  property).
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 17.2 and Theorem 17.3
  (statement: an abelian variety acquires semistable reduction after a finite extension).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the case of finite extensions of $\mathbb{Q}_p$, phrased with a
  semi-abelian group scheme over the integral closure of $\mathbb{Z}_p$ in a finite extension whose
  generic fibre is the given abelian variety, as `GlobalTheory.Published.SemistableReductionSt`.
