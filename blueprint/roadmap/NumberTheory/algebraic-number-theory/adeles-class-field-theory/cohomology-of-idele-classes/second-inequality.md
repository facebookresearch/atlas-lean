# Second inequality of global class field theory

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, let
$C_L = \mathbb{I}_L / L^\times$ be the idèle class group of $L$ with the action of $G$ induced by its
action on the idèles, and let $\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$ be the idèle norm,
$\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$. Then:

1. (second inequality) the index $(\mathbb{I}_K : K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L))$ is finite and
   divides $[L : K]$;
2. $H^1(G, C_L) = 0$;
3. $H^2(G, C_L)$ is finite, of order dividing $[L : K]$.

By the [Galois invariants of the idèle class group](galois-invariants-of-idele-classes.md), the index in
part 1 is the order of $C_K / \mathrm{Nm}_{L/K}(C_L) = \hat H^0(G, C_L)$.

Milne's proof. For cyclic $G$ the three statements are equivalent (Lemma VII.5.2): by the
[periodicity of Tate cohomology](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md),
$\hat H^0(G, C_L) \cong H^2(G, C_L)$ and $\hat H^{-1}(G, C_L) \cong H^1(G, C_L)$, and the
[first inequality](first-inequality.md) gives $h(C_L) = [L : K]$. Restriction to the Sylow subgroups,
which is injective on the $p$-primary components, reduces the theorem to $p$-groups (Lemma VII.5.3), and
an induction on $|G|$ reduces it to $G$ cyclic of prime order $p$ (Lemma VII.5.4). For a normal subgroup
$H$ of index $p$ with fixed field $K' = L^H$, the exact inflation–restriction sequences for $H^1$ and $H^2$
give parts 2 and 3 from the cases of $K'/K$ and $L/K'$. For part 1, $(C_K : \mathrm{Nm}_{L/K} C_L)$ is the
product of $(C_K : \mathrm{Nm}_{K'/K} C_{K'})$, which divides $p$ by the case of $K'/K$, and
$(\mathrm{Nm}_{K'/K} C_{K'} : \mathrm{Nm}_{L/K} C_L)$; the norm $\mathrm{Nm}_{K'/K}$ induces a surjection
$C_{K'} / \mathrm{Nm}_{L/K'} C_L \to \mathrm{Nm}_{K'/K} C_{K'} / \mathrm{Nm}_{L/K} C_L$, so the second index
divides $(C_{K'} : \mathrm{Nm}_{L/K'} C_L)$, which divides $[L : K']$ by induction.

For $G$ cyclic of prime order $p$ it suffices to prove the second inequality after adjoining a
primitive $p$-th root of unity $\zeta$ to $K$ and to $L$: the degree $m = [K(\zeta) : K]$ divides
$p - 1$, and the composite of the maps $C_K / \mathrm{Nm}(C_L) \to C_{K(\zeta)} / \mathrm{Nm}(C_{L(\zeta)})$
and $\mathrm{Nm}_{K(\zeta)/K}$ back is multiplication by $m$, an isomorphism on a group killed by $p$
(Lemma VII.6.1). The case of a field containing a primitive $p$-th root of unity is the
[Kummer case of the second inequality](second-inequality-kummer-case.md). Milne also notes that the
second inequality for all Galois extensions follows from his analytic Theorem VI.4.9.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Second inequality for Kummer extensions of prime exponent](second-inequality-kummer-case.md), for cyclic extensions of prime degree $p$ of a field containing a primitive $p$-th root of unity
- [First inequality of global class field theory](first-inequality.md), for the equivalence of the three statements for cyclic extensions
- [Galois invariants of the idèle class group](galois-invariants-of-idele-classes.md), for $\hat H^0(G, C_L) \cong \mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L)$
- [Periodicity of Tate cohomology for finite cyclic groups](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for restriction to Sylow subgroups and the inflation–restriction sequences

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VII.5.1 (the statement) and Lemmas
  VII.5.2–5.4 with their proofs; Lemma VII.6.1 and the rest of Section VII.6 (the algebraic proof of the
  second inequality for cyclic extensions of prime degree); the paragraph after Lemma VII.5.4 (the
  analytic alternative, Theorem VI.4.9 with Proposition V.4.6).
