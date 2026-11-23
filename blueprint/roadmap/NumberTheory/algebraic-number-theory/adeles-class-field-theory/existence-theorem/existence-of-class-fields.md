# Existence theorem of global class field theory

Let $K$ be a number field with idèle class group $C_K$, and fix an algebraic closure $\overline{K}$ of $K$.
For every open subgroup $N$ of finite index in $C_K$ there is a unique finite abelian extension
$L \subseteq \overline{K}$ of $K$ such that

$$\mathrm{Nm}_{L/K}(C_L) = N,$$

where $\mathrm{Nm}_{L/K} \colon C_L \to C_K$ is induced by the idèle norm. Thus the norm groups
$\mathrm{Nm}_{L/K}(C_L)$ of the finite abelian extensions of $K$ are exactly the open subgroups of finite
index of $C_K$, and $L \mapsto \mathrm{Nm}_{L/K}(C_L)$ is a bijection between the finite abelian extensions
of $K$ in $\overline{K}$ and these subgroups, with $L_1 \subseteq L_2$ if and only if
$\mathrm{Nm}_{L_1/K}(C_{L_1}) \supseteq \mathrm{Nm}_{L_2/K}(C_{L_2})$. The
[global Artin map](../reciprocity-law/global-artin-map.md) then induces $C_K / N \cong \mathrm{Gal}(L/K)$, by
the [global reciprocity law](../reciprocity-law/global-reciprocity-law.md). The openness hypothesis cannot be
dropped: $C_K$ has subgroups of finite index that are not open (Milne, Exercise V.5.11).

Milne proves existence by induction on the index of $N$ (Theorem VII.9.5). If the index is divisible by a
prime $p$, the [descent of norm groups](norm-group-descent.md) lets one replace $K$ by $K(\zeta_p)$, with
$\zeta_p$ a primitive $p$-th root of unity, and $N$ by its preimage under the norm. Then $N$ lies in an open
subgroup $N_1$ of index $p$, which by the [key case](existence-theorem-kummer-case.md) is the norm group of a
cyclic extension $K'/K$ of degree $p$; the preimage of $N$ in $C_{K'}$ has index $(C_K : N)/p$, so it is a
norm group by induction, and the descent of norm groups again shows that $N$ is one. Every norm group is
open, since it contains the image of an [open norm group of idèles](../cohomology-of-idele-classes/idele-norm-group-is-open.md),
and has index $[L : K]$ by the reciprocity law. Uniqueness and the reversal of inclusions follow from the
reciprocity law as in the local case (Milne, Corollary I.1.2): the norm group of a composite $L_1 L_2$ is
the intersection of the norm groups of $L_1$ and $L_2$, because $\mathrm{Gal}(L_1 L_2/K)$ embeds in
$\mathrm{Gal}(L_1/K) \times \mathrm{Gal}(L_2/K)$ and the global Artin maps are compatible with restriction;
so $\mathrm{Nm}(C_{L_1}) \supseteq \mathrm{Nm}(C_{L_2})$ makes $L_1 L_2$ and $L_2$ have the same norm group,
hence the same degree over $K$, and $L_1 \subseteq L_2$.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)
- [Global Artin map](../reciprocity-law/global-artin-map.md), for the isomorphism $C_K / N \cong \mathrm{Gal}(L/K)$; the proof also uses its compatibility with restriction

## Proof depends on

- [Key case of the existence theorem](existence-theorem-kummer-case.md)
- [Norm groups descend along finite extensions](norm-group-descent.md)
- [Global reciprocity law](../reciprocity-law/global-reciprocity-law.md), for the index of norm groups, the cyclic extension of the key case, uniqueness and the reversal of inclusions
- [Norm groups of finite extensions are open in the idèle group](../cohomology-of-idele-classes/idele-norm-group-is-open.md), for the openness of norm groups

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem V.5.5 (Existence Theorem) and Corollary V.5.6
  (the statement); Section VII.9, Theorem 9.5 and its proof (stated there for subgroups of finite index;
  the induction uses Lemmas 9.3 and 9.4, which concern open subgroups) and Lemma 9.4; Exercise V.5.11;
  Corollary I.1.2 and its proof (the same argument for local fields).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Theorem 28.6 (Global Existence Theorem)
  and Theorem 28.7 (the inclusion-reversing bijection and the isomorphisms $C_K/H \cong \mathrm{Gal}(L/K)$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as
  `GroundTheory.Global.exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex`.
