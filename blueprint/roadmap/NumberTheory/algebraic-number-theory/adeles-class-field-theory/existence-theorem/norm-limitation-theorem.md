# Norm limitation theorem

Let $E/K$ be a finite extension of number fields, not necessarily Galois, and let $M$ be the largest
subfield of $E$ containing $K$ such that $M/K$ is abelian Galois. Then the norm groups of $E$ and of $M$ in
the idèle class group $C_K$ coincide:

$$\mathrm{Nm}_{E/K}(C_E) = \mathrm{Nm}_{M/K}(C_M),$$

where $\mathrm{Nm}_{E/K} \colon C_E \to C_K$ is induced by the idèle norm,
$\mathrm{Nm}_{E/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{E_w/K_v}(b_w)$. So the norm groups of non-abelian
extensions are norm groups of abelian ones.

Milne's proof. Let $L$ be a finite Galois extension of $K$ containing $E$, with $G = \mathrm{Gal}(L/K)$ and
$H = \mathrm{Gal}(L/E)$. Cup product with the [fundamental classes](../reciprocity-law/fundamental-class.md)
of $L/K$ and $L/E$ gives isomorphisms $G^{\mathrm{ab}} \cong C_K / \mathrm{Nm}_{L/K}(C_L)$ and
$H^{\mathrm{ab}} \cong C_E / \mathrm{Nm}_{L/E}(C_L)$, compatible with corestriction, under which the map
$H^{\mathrm{ab}} \to G^{\mathrm{ab}}$ induced by the inclusion corresponds to $\mathrm{Nm}_{E/K}$. Hence
$C_K / \mathrm{Nm}_{E/K}(C_E)$ is isomorphic to the cokernel of $H^{\mathrm{ab}} \to G^{\mathrm{ab}}$, which is
$G / [G, G] H = \mathrm{Gal}(M/K)$; by the [global reciprocity law](../reciprocity-law/global-reciprocity-law.md)
this has the order of $C_K / \mathrm{Nm}_{M/K}(C_M)$. Since $\mathrm{Nm}_{E/K}(C_E) \subseteq \mathrm{Nm}_{M/K}(C_M)$
by transitivity of norms, the two groups are equal.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Fundamental class of global class field theory](../reciprocity-law/fundamental-class.md), for the reciprocity isomorphisms of the Galois extensions $L/K$ and $L/E$ and their compatibility with corestriction
- [Global reciprocity law](../reciprocity-law/global-reciprocity-law.md), for the abelian extension $M/K$

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VIII.4.8 (the norm limitation theorem) and
  its proof; Theorem V.3.16 (the statement in terms of ideals).
