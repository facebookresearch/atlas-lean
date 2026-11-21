# Tate cohomology of the idèle class group of a cyclic extension

Let $L/K$ be a cyclic extension of number fields of degree $n$, with Galois group $G$, and let
$C_L = \mathbb{I}_L / L^\times$ be the idèle class group of $L$, on which $G$ acts through its action
on the idèles. Then

$$|\hat H^0(G, C_L)| = n \qquad \text{and} \qquad \hat H^{-1}(G, C_L) = 0.$$

The natural map $C_K \to C_L$ identifies $C_K$ with the invariants $C_L^G$ (Milne, Lemma VII.4.1),
so $\hat H^0(G, C_L) = C_K / \mathrm{Nm}_{L/K}(C_L) \cong \mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L)$,
and the first statement says that the norm index $(\mathbb{I}_K : K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L))$
equals $n$: it is at least $n$ by the first inequality and at most $n$ by the second inequality of
global class field theory. By the periodicity of Tate cohomology of cyclic groups,
$\hat H^{-1}(G, C_L) \cong \hat H^1(G, C_L) = H^1(G, C_L)$, so the second statement says
$H^1(G, C_L) = 0$, as in Milne's Theorem VII.5.1(b).

Milne's proof first shows that the Herbrand quotient of $C_L$ is $n$ (Theorem VII.4.3). Choose a
finite set $S$ of places of $K$ containing the infinite places, the places that ramify in $L$ and the
places below a set of prime ideals generating the class group of $L$, and let $T$ be the set of places
of $L$ above $S$. Then $C_L \cong \mathbb{I}_{L,T} / U(T)$, where $\mathbb{I}_{L,T}$ is the group of
idèles that are units outside $T$ and $U(T)$ the group of $T$-units of $L$, so multiplicativity of the
Herbrand quotient gives $h(C_L) = h(\mathbb{I}_{L,T}) / h(U(T))$. The local computation
$h(\mathbb{I}_{L,T}) = \prod_{v \in S} n_v$, with $n_v$ the local degrees (Proposition VII.2.7), and the
unit computation $h(U(T)) = n^{-1} \prod_{v \in S} n_v$ (Proposition VII.3.1, from Dirichlet's
$S$-unit theorem) give $h(C_L) = n$. The second inequality, that
$(\mathbb{I}_K : K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L))$ divides $[L : K]$ (Theorem VII.5.1(a)),
reduces to cyclic extensions of prime degree $p$ of a field containing the $p$-th roots of unity, where
Milne proves it with Kummer theory (Section VII.6); Theorem VI.4.9 gives an analytic proof. Then
$|\hat H^0(G, C_L)| = n \, |\hat H^{-1}(G, C_L)| \ge n$ and $|\hat H^0(G, C_L)| \le n$ give both
statements (Lemma VII.5.2).

## Depends on

- [Topological idele class group](adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Multiplicativity of the Herbrand quotient in short exact sequences](../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-mul-of-short-exact.md)
- [Herbrand quotient as a ratio of orders](../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-eq.md)
- [Periodicity of Tate cohomology for finite cyclic groups](../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter VII: Lemma 4.1, Theorem 4.3 and its
  proof, Corollary 4.4 (first inequality), Theorem 5.1 and Lemma 5.2 (for cyclic $G$, the second
  inequality, $H^1(G, C_L) = 0$ and $|H^2(G, C_L)| = [L : K]$ are equivalent, and the index equals
  $[L : K]$), Section 6 (algebraic proof of the second inequality).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>,
  no licence) uses this result, as `GroundTheory.Global.natCard_cycTateZero_ideleClassGroup_eq_finrank`
  and `GroundTheory.Global.natCard_cycTateNegOne_ideleClassGroup`, derived from its
  `GroundTheory.Global.firstInequality` and `GroundTheory.Global.secondInequality`.
