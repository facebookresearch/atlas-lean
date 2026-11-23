# A solvable extension with norms dense modulo principal idèles is trivial

Let $L/K$ be a finite Galois extension of number fields with solvable Galois group, and let
$\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$ be the idèle norm,
$\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$. Suppose that there is a subgroup
$D$ of $\mathbb{I}_K$ such that

- $D \subseteq \mathrm{Nm}_{L/K}(\mathbb{I}_L)$, and
- $K^\times D$ is dense in $\mathbb{I}_K$.

Then $L = K$.

Milne's proof: if $L \neq K$, solvability gives a subfield $K' \subseteq L$ with $K'/K$ cyclic of degree
$> 1$. By transitivity of norms, $D \subseteq \mathrm{Nm}_{K'/K}(\mathbb{I}_{K'})$, so
$K^\times \mathrm{Nm}_{K'/K}(\mathbb{I}_{K'})$ is a dense subgroup of $\mathbb{I}_K$; it is open, since it
contains the [open norm group](idele-norm-group-is-open.md), hence closed, hence all of $\mathbb{I}_K$.
This contradicts the [first inequality](first-inequality.md),
$(\mathbb{I}_K : K^\times \mathrm{Nm}_{K'/K}(\mathbb{I}_{K'})) \ge [K' : K]$.

## Depends on

- [Topological idele group](../adeles-and-ideles/topological-idele-group.md)

## Proof depends on

- [First inequality of global class field theory](first-inequality.md), for the cyclic extension $K'/K$
- [Norm groups of finite extensions are open in the idèle group](idele-norm-group-is-open.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Lemma VII.4.5 (the statement, for $L$ a finite
  solvable extension of $K$) and its proof.
