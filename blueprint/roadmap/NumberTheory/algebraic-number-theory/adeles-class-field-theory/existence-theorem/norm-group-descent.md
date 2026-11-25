# Norm groups descend along finite extensions

Let $K$ be a number field, $U$ an open subgroup of finite index in its idèle class group $C_K$, and $K'/K$ a
finite extension, with norm map $\mathrm{Nm}_{K'/K} \colon C_{K'} \to C_K$ induced by the idèle norm. If
$\mathrm{Nm}_{K'/K}^{-1}(U)$ is a norm group in $C_{K'}$, that is,
$\mathrm{Nm}_{K'/K}^{-1}(U) = \mathrm{Nm}_{L/K'}(C_L)$ for some finite abelian extension $L/K'$, then $U$ is a
norm group in $C_K$.

Milne's proof: let $M$ be the largest subfield of $L$ that is abelian over $K$. By the
[norm limitation theorem](norm-limitation-theorem.md) for $L/K$ and transitivity of norms,
$\mathrm{Nm}_{M/K}(C_M) = \mathrm{Nm}_{L/K}(C_L) = \mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}(C_L)) \subseteq U$, so $U$
contains a norm group and is one because
[subgroups containing a norm group are norm groups](overgroups-of-norm-groups.md).

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Norm limitation theorem](norm-limitation-theorem.md), for the extension $L/K$
- [Subgroups containing a norm group are norm groups](overgroups-of-norm-groups.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Lemma VII.9.4 (the statement) and its proof, which
  assumes the norm limitation theorem (Theorem VIII.4.8), and the remark before it (Tate's proof in
  Cassels and Fröhlich, p. 202, avoids that theorem).
