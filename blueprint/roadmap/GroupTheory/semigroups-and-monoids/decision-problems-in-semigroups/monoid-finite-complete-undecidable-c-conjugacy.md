# Some monoid with a finite complete presentation has undecidable c-conjugacy problem

There is a monoid given by a finite complete (noetherian and confluent) rewriting system whose $c$-conjugacy problem is undecidable, although such monoids have decidable word problem.

Let $M$ be a monoid. If $M$ has a zero, for $a \in M \setminus \{0\}$ let $\mathbb{P}(a) = \{ g \in M : \text{for all } m \in M,\ mag = 0 \Rightarrow ma = 0 \}$ and $\mathbb{P}(0) = \{0\}$; if $M$ has no zero, let $\mathbb{P}(a) = M$ for all $a$. Elements $a, b$ are $c$-conjugate, $a \sim_c b$, when there exist $g \in \mathbb{P}(a)$ and $h \in \mathbb{P}(b)$ with $ag = gb$ and $bh = ha$; this is an equivalence relation. For a monoid $M = \Sigma^* / {\leftrightarrow_R^*}$ given by a finite alphabet $\Sigma$ and finite rewriting system $R$, the $c$-conjugacy problem asks for an algorithm that decides, for words $u, v \in \Sigma^*$, whether $[u] \sim_c [v]$.

There exist a finite alphabet $\Sigma$ and a finite rewriting system $R$ on $\Sigma^*$ that is complete, that is noetherian (no infinite chain of rewritings) and confluent, such that the monoid defined by $(\Sigma; R)$ has undecidable $c$-conjugacy problem (Proposition 4.2 of the source).

## Depends on

- [The word problem of a Thue system](../../../TheoryOfComputation/undecidable-problems/string-rewriting-systems/thue-wp.md)
- [Abstract reduction system](../../../Logic/first-order-logic/term-rewriting/abstract-reduction-system.md)
- [Confluence of a relation](../../../Logic/first-order-logic/term-rewriting/confluence-of-a-relation.md)

## Proof depends on

None.

## Expansion

Narendran and Otto constructed a finite complete presentation of a monoid $M$, without a zero, whose $o$-conjugacy problem is undecidable, where $a \sim_o b$ means $ag = gb$ and $bh = ha$ for some $g, h \in M$. Adjoining a zero gives a monoid $M^0$ that still has a finite complete presentation, and in $M^0$ the relation $\sim_c$ is $\sim_o$ of $M$ together with the pair $(0, 0)$; so $M^0$ has undecidable $c$-conjugacy problem. A finite complete presentation has decidable word problem, by reducing both words to their normal forms, so the theorem separates the $c$-conjugacy problem from the word problem.

## Sources

- J. Araújo, M. Kinyon, J. Konieczny and A. Malheiro, "Decidability and independence of conjugacy problems in finitely presented monoids", Theoretical Computer Science 731 (2018), 88–98, https://doi.org/10.1016/j.tcs.2018.04.002; arXiv:1703.00027v1 (Proposition 4.2 of arXiv:1703.00027v1, with the definition of $\sim_c$ in Section 1).
