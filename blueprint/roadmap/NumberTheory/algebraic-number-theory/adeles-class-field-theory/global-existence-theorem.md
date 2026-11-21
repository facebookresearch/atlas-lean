# Existence theorem of global class field theory

Let $K$ be a number field with idèle class group $C_K$, and fix an algebraic closure $\overline{K}$ of
$K$. For every open subgroup $N$ of finite index in $C_K$ there is a unique finite abelian extension
$L \subseteq \overline{K}$ of $K$ such that

$$\mathrm{Nm}_{L/K}(C_L) = N.$$

Thus the norm groups $\mathrm{Nm}_{L/K}(C_L)$ of the finite abelian extensions of $K$ are exactly the
open subgroups of finite index of $C_K$, and $L \mapsto \mathrm{Nm}_{L/K}(C_L)$ is a bijection between
the finite abelian extensions of $K$ in $\overline{K}$ and these subgroups, which reverses inclusions
(Milne, Corollary V.5.6). With [global Artin reciprocity](global-artin-reciprocity.md), the Artin map
then induces $C_K / N \cong \mathrm{Gal}(L/K)$.

Milne's proof (Section VII.9) first shows that a subgroup of $C_K$ containing a norm group is a norm
group (Lemma VII.9.1, from the reciprocity law). The key case is an open subgroup $V$ such that
$C_K / V$ is killed by a prime $p$, when $K$ contains a primitive $p$-th root of unity: $V$ contains
the norm group of the Kummer extension obtained by adjoining the $p$-th roots of the $S$-units, for a
suitable finite set $S$ of places (Lemma VII.9.3). An induction on the index, adjoining roots of unity
and using the norm limitation theorem (Lemma VII.9.4), gives the general case (Theorem VII.9.5).

## Depends on

- [Topological idele class group](adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Global Artin reciprocity](global-artin-reciprocity.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem V.5.5 (Existence Theorem) and
  Corollary V.5.6 (the statement); Section VII.9, Lemmas 9.1, 9.3 and 9.4 and Theorem 9.5 (the proof).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Theorem 28.6 (Global Existence
  Theorem) and Theorem 28.7.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>,
  no licence) uses this result, as
  `GroundTheory.Global.exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex`.
