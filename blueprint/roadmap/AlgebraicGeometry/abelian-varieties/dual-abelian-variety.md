# Dual abelian variety

Let $A$ be an [abelian variety](abelian-scheme.md) over a field $k$, with zero $0$, and let
$\operatorname{Pic}^0(A)$ be the set of isomorphism classes of invertible sheaves $L$ on $A$ such that
$t_a^* L \cong L$ on $A_{\bar k}$ for every $a \in A(\bar k)$, where $\bar k$ is an algebraic closure
of $k$ and $t_a$ is translation by $a$; equivalently $m^* L \cong p^* L \otimes q^* L$ on $A \times A$,
with $m$ the group law and $p$, $q$ the projections.

A **dual abelian variety** of $A$ is a pair $(A^\vee, P)$ of a variety $A^\vee$ over $k$ and an
invertible sheaf $P$ on $A \times A^\vee$, the Poincaré sheaf, such that $P|_{A \times \{b\}}$ lies in
$\operatorname{Pic}^0$ for every point $b$ of $A^\vee$ and $P|_{\{0\} \times A^\vee}$ is trivial, and
which is universal: for every variety $T$ over $k$ and every invertible sheaf $L$ on $A \times T$ with
$L|_{A \times \{t\}}$ in $\operatorname{Pic}^0$ for all points $t$ of $T$ and $L|_{\{0\} \times T}$
trivial, there is a unique morphism $\alpha \colon T \to A^\vee$ with
$(1 \times \alpha)^* P \cong L$. Then:

1. The dual abelian variety exists, is unique up to unique isomorphism, is an abelian variety of the
   same dimension as $A$, and its formation commutes with extension of scalars; working with schemes,
   $(A^\vee, P)$ has the universal property for every $k$-scheme $T$.
2. $A^\vee(k) = \operatorname{Pic}^0(A)$: every class in $\operatorname{Pic}^0(A)$ is represented
   exactly once by $P|_{A \times \{b\}}$ with $b \in A^\vee(k)$.
3. (Biduality.) Let $B$ be an abelian variety and $L$ an invertible sheaf on $A \times B$ whose
   restrictions to $\{0\} \times B$ and $A \times \{0\}$ are trivial, and let
   $s \colon A \times B \to B \times A$ be the switch. The following are equivalent: $(B, L)$ is the
   dual of $A$; if $L|_{A \times \{b\}}$ is trivial then $b = 0$; if $L|_{\{a\} \times B}$ is trivial
   then $a = 0$; $(A, s^* L)$ is the dual of $B$. In particular $(A, s^* P)$ is the dual of
   $A^\vee$, so $A^{\vee\vee} \cong A$.

In characteristic zero Milne constructs $A^\vee$ as the quotient $A / K(L)$ of $A$ by the finite group
$K(L)$ attached to an ample invertible sheaf $L$, using the surjectivity of $\varphi_L$ onto
$\operatorname{Pic}^0(A)$; in positive characteristic $K(L)$ is replaced by a finite subgroup scheme,
following Mumford's *Abelian Varieties*, Chapter III.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field

## Proof depends on

- [Line bundles on abelian varieties](line-bundles-on-abelian-varieties.md), for the theorem of the
  square, quotients by finite groups and the surjectivity of $\varphi_L$ onto
  $\operatorname{Pic}^0(A)$
- [Abelian varieties are projective](abelian-varieties-are-projective.md), for the ample invertible
  sheaf used in the construction

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §8: Proposition 8.4 and the definition
  of $\operatorname{Pic}^0(A)$, the definition of the dual abelian variety and the Poincaré sheaf,
  Remark 8.7 (a)–(e), Lemma 8.8, Theorem 8.9 (with its proof referred to Mumford, p. 81) and the
  construction of the dual in characteristic zero, Remark 8.12 and the paragraph on positive
  characteristic (referring to Mumford, Chapter III).
- D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research Studies in Mathematics 5,
  Oxford University Press, 1970: Chapter III (as cited by Milne).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses a form of this result for abelian schemes over an arbitrary
  base, with a Poincaré sheaf and biduality, as `GlobalTheory.Published.DualAbelianScheme`.
