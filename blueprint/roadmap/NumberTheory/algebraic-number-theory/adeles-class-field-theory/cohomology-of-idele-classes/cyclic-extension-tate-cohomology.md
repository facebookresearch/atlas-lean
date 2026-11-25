# Tate cohomology of the idèle class group of a cyclic extension

Let $L/K$ be a cyclic extension of number fields of degree $n$, with Galois group $G$, and let
$C_L = \mathbb{I}_L / L^\times$ be the idèle class group of $L$, on which $G$ acts through its action on
the idèles. Then

$$|\hat H^0(G, C_L)| = n \qquad \text{and} \qquad \hat H^{-1}(G, C_L) = 0.$$

Equivalently, with the idèle norm $\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$,
$\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$: the norm index
$(\mathbb{I}_K : K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L))$ equals $n$, and $H^1(G, C_L) = 0$; also
$|H^2(G, C_L)| = n$.

By the [Galois invariants of the idèle class group](galois-invariants-of-idele-classes.md),
$\hat H^0(G, C_L) = C_K / \mathrm{Nm}_{L/K}(C_L) \cong \mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L)$,
and by the
[periodicity of Tate cohomology](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md)
of the cyclic group $G$, $\hat H^{-1}(G, C_L) \cong H^1(G, C_L)$ and $\hat H^0(G, C_L) \cong H^2(G, C_L)$.
The [second inequality](second-inequality.md) gives $H^1(G, C_L) = 0$ and an index dividing $n$, and the
[first inequality](first-inequality.md), $|\hat H^0(G, C_L)| = n \, |\hat H^{-1}(G, C_L)|$, then gives
equality (Milne, Lemma VII.5.2).

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [First inequality of global class field theory](first-inequality.md)
- [Second inequality of global class field theory](second-inequality.md)
- [Galois invariants of the idèle class group](galois-invariants-of-idele-classes.md)
- [Periodicity of Tate cohomology for finite cyclic groups](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter VII: Lemma 4.1, Theorem 4.3 and Corollary
  4.4 (first inequality), Theorem 5.1 and Lemma 5.2 (for cyclic $G$, the second inequality,
  $H^1(G, C_L) = 0$ and $|H^2(G, C_L)| = [L : K]$ are equivalent, and the index equals $[L : K]$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.natCard_cycTateZero_ideleClassGroup_eq_finrank`
  and `GroundTheory.Global.natCard_cycTateNegOne_ideleClassGroup`, derived from its
  `GroundTheory.Global.firstInequality` and `GroundTheory.Global.secondInequality`.
