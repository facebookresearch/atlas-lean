# The global Artin map is trivial on principal idèles

Let $L/K$ be a finite abelian extension of number fields. Then the
[global Artin map](global-artin-map.md) $\phi_{L/K} \colon \mathbb{I}_K \to \mathrm{Gal}(L/K)$ satisfies
$\phi_{L/K}(a) = 1$ for every principal idèle $a \in K^\times$. Equivalently, the global Artin map
$\phi_K \colon \mathbb{I}_K \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ is trivial on $K^\times$, so it factors
through the idèle class group $C_K = \mathbb{I}_K / K^\times$.

Milne's proof (Lemma VII.8.5). Let $G = \mathrm{Gal}(L/K)$, $a \in K^\times = H^0(G, L^\times)$ and
$\chi \in \mathrm{Hom}(G, \mathbb{Q}/\mathbb{Z})$, with image $\delta\chi \in H^2(G, \mathbb{Z})$ under the
connecting map of $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$. The global Artin map is
the product of the local ones, and by the local cup-product formula
$\chi(\phi_v(a)) = \mathrm{inv}_v((a \cup \delta\chi)_v)$ at every place $v$ (at a real place that
becomes complex in $L$ it is the formula for $\mathbb{C}/\mathbb{R}$; at a complex place, or a real place
that stays real, both sides vanish), so
$\chi(\phi_{L/K}(a)) = \sum_v \mathrm{inv}_v((a \cup \delta\chi)_v)$, which is $0$ because
[the local invariants of the global class](sum-of-local-invariants.md) $a \cup \delta\chi \in H^2(G, L^\times)$
sum to zero. As the characters of the finite abelian group $G$ separate its elements,
$\phi_{L/K}(a) = 1$.

## Depends on

- [Global Artin map](global-artin-map.md)

## Proof depends on

- [The local invariants of a global class in H² sum to zero](sum-of-local-invariants.md)
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local cup-product formula at every place, the real ones included (its item 3)
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for the compatibility of cup products with restriction to the decomposition groups (its item 3)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VII.8.1(a) (the statement) and Lemma VII.8.5
  (statement (b) of Theorem VII.8.1 implies statement (a)) with its proof; Proposition III.3.6.
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Theorem 28.4 (the kernel of the global
  Artin homomorphism contains $K^\times$).
