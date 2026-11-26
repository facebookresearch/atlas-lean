# Semistable reduction theorem for abelian varieties

Let $k$ be a field with algebraic closure $\bar k$. The [split torus](split-torus.md) of rank $r$
over $k$ is $\mathbb{G}_m^r = \operatorname{Spec} k[\mathbb{Z}^r]$, with the group law of the Hopf
algebra $k[\mathbb{Z}^r]$. A [torus](is-torus.md) over $k$ is a group scheme $T$ over $k$ whose base
change $T_{\bar k}$ is isomorphic, as a group scheme, to a split torus over $\bar k$. A group scheme
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
choice; Néron models of abelian varieties exist, so the definition asks only about $X_v^0$.

**Theorem** (Grothendieck). Let $X$ be an abelian variety over a field $F$ and $v$ a discrete
valuation on $F$, with valuation ring $\mathcal{O}$. There is a finite Galois extension $L$ of $F$,
inside an algebraic closure $\bar F$ of $F$, such that $X_L$ has semistable reduction at every
extension of $v$ to $L$: at every valuation ring $w$ of $L$ with $w \cap F = \mathcal{O}$.

Silverberg and Zarhin print the conclusion as "$X$ has semistable reduction at the extensions of $v$
to $L$", with $X$ over $L$, that is $X_L$. Every finite extension of $F$ embeds in $\bar F$, so taking
$L$ inside $\bar F$ loses nothing. The valuation rings of $L$ that meet $F$ in $\mathcal{O}$ are the
extensions of $v$ to $L$. They are the localizations of the integral closure of $\mathcal{O}$ in $L$ at
its maximal ideals, hence discrete valuation rings, and the theorem takes each of them with that
structure.

Conrad states the theorem with a finite separable extension $K'/K$ such that $A_{K'}$ has semistable
reduction over the integral closure $R'$ of $R$ in $K'$, that is, at the localization of $R'$ at each
of its maximal ideals. The two forms are the same theorem. A finite Galois extension is separable.
Conversely, let $L$ be a Galois closure of $K'$: every extension of $v$ to $L$ lies over an extension
of $v$ to $K'$, and semistable reduction persists under such an extension of discrete valuation
rings, since the identity component of the Néron model then commutes with base change (Conrad,
Corollary 4.5) and an extension of an abelian variety by a torus stays one after extending the
residue field. Conrad's Proposition 6.5 gives such a Galois extension directly: for $N \ge 3$ prime to
the residue characteristic, $A$ acquires semistable reduction at all places of $K(A[N])$. Conrad
calls a smooth connected commutative $k$-group semi-abelian when its base change to $\bar k$ is an
extension of an abelian variety by a torus, and says that $A$ has semistable reduction when
$(\mathcal{A}_k)^0$ is semi-abelian; by his Theorem 3.1 the torus and the extension then descend to
$k$, which is the form above.

Conrad proves the theorem by reducing it to Jacobians of smooth proper geometrically connected
curves: semistable reduction is invariant under isogenies (Proposition 4.1) and products, and by
Bertini slicing and Poincaré's reducibility theorem every abelian variety $A$ has an abelian variety
$B$ with $A \times B$ isogenous to such a Jacobian (Proposition 4.3). For a Jacobian he uses the semistable reduction theorem for curves
and Raynaud's theorem that $\operatorname{Pic}^0_{X/S}$ of a regular proper flat semistable curve over
$R$ with smooth generic fibre is a separated scheme (Theorem 7.13), whose special fibre is
semi-abelian (Proposition 7.14) and which, by the open immersion criterion of Theorem 4.4, is the
identity component of the Néron model of its generic fibre.

## Informally uses

- [Néron model of an abelian variety](../neron-model.md), for the existence of Néron models of
  abelian varieties and the base change of their identity components (Conrad, Theorem 4.4 and
  Corollary 4.5)
- [Representability of relative Picard functors](../representability-of-picard-functors.md), for
  the Picard scheme of a semistable curve in Conrad's proof for Jacobians (Conrad, §7)

## Sources

- A. Silverberg and Yu. G. Zarhin, "Semistable reduction and torsion subgroups of abelian
  varieties", *Ann. Inst. Fourier* 45 (1995), 403–420, <https://doi.org/10.5802/aif.1459>: §3,
  pp. 404–405, the Néron model and Definition 3.1 (ii) (semistable reduction: $X_v^0$ is an extension
  of an abelian variety by an affine torus); Theorem 3.4, pp. 405–406 (the theorem as stated here),
  whose proof they cite as Proposition 3.6 of SGA 7 I, Exp. IX, where it is Théorème 3.6.
- A. Grothendieck, "Modèles de Néron et monodromie", Exposé IX in *Groupes de monodromie en géométrie
  algébrique* (SGA 7 I), Lecture Notes in Mathematics 288, Springer, 1972, 313–523: Théorème 3.6.
- B. Conrad, "Semistable reduction for abelian varieties", seminar notes, Stanford, 2011,
  <http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf>: §2, Definition 2.10 (tori); §3, the
  definition of semi-abelian varieties and Theorem 3.1 (descent of the torus); §4, the definition of
  semistable reduction over a discrete valuation ring and over a semi-local Dedekind ring,
  Theorem 4.2 (semistable reduction after a finite separable extension, over the integral closure;
  the integral closure "of $R$ in $K$" there is a misprint for $K'$), the remarks after it,
  Propositions 4.1 and 4.3, Theorem 4.4 and Corollary 4.5 with the discussion after it; §6,
  Proposition 6.5; §7, Theorem 7.13 and Proposition 7.14.
- S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, Ergebnisse der Mathematik (3) 21,
  Springer, 1990: §1.2, Definition 1 (Néron models are of finite type).
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Remark 17.2 and Theorem 17.3
  (statement: an abelian variety acquires semistable reduction after a finite extension).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the case of finite extensions of $\mathbb{Q}_p$, phrased with a
  semi-abelian group scheme over the integral closure of $\mathbb{Z}_p$ in a finite extension whose
  generic fibre is the given abelian variety, as `GlobalTheory.Published.SemistableReductionSt`.
