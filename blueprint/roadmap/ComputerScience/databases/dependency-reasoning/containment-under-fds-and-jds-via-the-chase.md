# Containment of tableau queries under functional and join dependencies via the chase

For tableau queries $(T_1, t_1)$ and $(T_2, t_2)$ without constants over a relation schema $R$ and a set $F$ of functional and join
dependencies over $R$, write $(T_1, t_1) \subseteq_F (T_2, t_2)$ when $(T_1, t_1)(I) \subseteq (T_2, t_2)(I)$ for every
instance $I$ of $R$ satisfying $F$, and $\equiv_F$ for containment both ways. Then
$(T_1, t_1) \subseteq_F (T_2, t_2)$ if and only if $\mathrm{chase}(T_1, t_1, F) \subseteq \mathrm{chase}(T_2, t_2, F)$
(containment on all instances), and $(T_1, t_1) \equiv_F (T_2, t_2)$ if and only if the two chases are equivalent.
Without constants the chase never fails. With constants it can: for $F = \{A \to B\}$ the Boolean tableau with rows
$(k, a)$ and $(k, b)$, $a \ne b$, would need $a$ and $b$ identified, so it has no match on any instance satisfying $F$ and
no ordinary tableau is its chase.

## Depends on

- [Chasing tableau queries with functional and join dependencies](../dependencies-and-the-chase/chasing-tableau-queries-with-functional-and-join-dependencie.md)

## Proof depends on

- [Chasing tableau queries with functional and join dependencies](../dependencies-and-the-chase/chasing-tableau-queries-with-functional-and-join-dependencie.md)
- [Chandra-Merlin containment criterion](../conjunctive-queries-and-the-chandra-merlin-theor/contained-iff-hom.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the restriction to tableau queries with no constants at the start of Section 8.4 (p. 175) and Theorem 8.4.8 (p. 177).
