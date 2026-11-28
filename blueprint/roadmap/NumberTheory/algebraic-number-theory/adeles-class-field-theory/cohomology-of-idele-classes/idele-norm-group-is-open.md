# Norm groups of finite extensions are open in the idèle group

Let $L/K$ be a finite extension of number fields and let
$\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$ be the idèle norm,
$\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$ for each place $v$ of $K$. Then
$\mathrm{Nm}_{L/K}(\mathbb{I}_L)$ contains an open subgroup of $\mathbb{I}_K$, and is therefore an open
subgroup of $\mathbb{I}_K$. More precisely, there is a finite set $S$ of places of $K$, containing the
infinite places and the places that ramify in $L$, and open subgroups $V_v \subseteq K_v^\times$ for
$v \in S$, such that

$$\prod_{v \in S} V_v \times \prod_{v \notin S} \mathcal{O}_v^\times \subseteq \mathrm{Nm}_{L/K}(\mathbb{I}_L).$$

Consequently every subgroup of $\mathbb{I}_K$ containing $\mathrm{Nm}_{L/K}(\mathbb{I}_L)$, such as
$K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L)$, is open, and hence also closed.

For each place $w \mid v$ the image of $\prod_{w \mid v} L_w^\times$ contains the local norm group
$\mathrm{Nm}_{L_w/K_v}(L_w^\times)$. This group contains the $[L_w : K_v]$-th powers, so it is an open
subgroup of finite index in $K_v^\times$, and when $L_w/K_v$ is unramified it contains
$\mathcal{O}_v^\times$, since the norm of an unramified extension of local fields maps units onto
units.

## Depends on

- [Topological idele group](../adeles-and-ideles/topological-idele-group.md)

## Proof depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the surjectivity of the norm on units in unramified extensions (its item 1) and for the openness of subgroups of finite index of $K_v^\times$ (its item 4)
- [Index of the n-th powers in a local field of characteristic zero](../../../p-adic-numbers/index-of-n-th-powers.md), for the finite index of the $[L_w : K_v]$-th powers

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition VII.2.8 (for $L/K$ Galois) and the
  paragraph before it; Proposition V.4.12 and Corollary V.4.13 (for every finite extension, the norm
  group contains a group $W_{\mathfrak{m}}$, which is open); Lemma I.1.3 and 1.7 (in characteristic $0$
  a subgroup of finite index of $K_v^\times$ is open).
