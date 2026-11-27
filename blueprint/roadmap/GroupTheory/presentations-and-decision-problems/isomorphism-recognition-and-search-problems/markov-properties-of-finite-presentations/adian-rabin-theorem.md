# Adian–Rabin theorem: Markov properties of finitely presented groups are undecidable

No algorithm decides, given a finite presentation, whether the presented group has a Markov property: a property of finitely presented groups that some finitely presented group has, while some finitely presented group embeds in no finitely presented group having it.

A *property* of finitely presented groups is one that depends only on the isomorphism type of the group, not on the presentation. A property $P$ is a *Markov property* if

1. there is a finitely presented group $G_1$ with $P$, and
2. there is a finitely presented group $G_2$ that cannot be embedded in any finitely presented group with $P$.

**Theorem (Adian; Rabin).** For every Markov property $P$, there is no algorithm that decides, given a finite presentation, whether the group it presents has $P$.

Conventions: the input is a finite presentation $\langle x_1, \dots, x_n \mid r_1, \dots, r_m \rangle$, and the property is fixed. Every property inherited by finitely presented subgroups that fails for some finitely presented group and holds for some finitely presented group is a Markov property, because a group without it cannot embed in a group with it.

## Depends on

- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Fix $G_1$ and $G_2$ as in the definition, and a finitely presented group $U_0$ with unsolvable word problem; replacing it by the free product $U = U_0 * G_2$, which is still finitely presented with unsolvable word problem and contains $G_2$, we may assume that $G_2 \le U$. For each word $w$ in the generators of $U_0$ one effectively constructs a finite presentation of a group $K_w$ such that $K_w$ is trivial when $w = 1$ in $U$, while $U$ and hence $G_2$ embed in $K_w$ otherwise; the construction uses free products, HNN extensions and amalgamated products, and its verification uses their normal form theorems (Britton's lemma), which have no page here. The group $G_1 * K_w$ is then isomorphic to $G_1$, which has $P$, when $w = 1$, and contains $G_2$, so does not have $P$, when $w \ne 1$. An algorithm deciding $P$ would therefore solve the word problem of $U_0$.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the definition of a Markov property and the statement are in its Section 6.4 ("Properties of groups"), the statement being Theorem 6.2 there.
- Michael O. Rabin, *Recursive unsolvability of group theoretic problems*, Ann. of Math. (2) 67 (1958), no. 1, 172–194, https://doi.org/10.2307/1969933, cited beside the survey read above; Adian's independent proofs appeared in 1955–1957 in Russian.
