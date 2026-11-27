# Incomplete databases, possible worlds and certain answers

A naive table is a database instance whose entries are constants or marked nulls. A valuation $v$ maps
each null to a constant; applying it to a naive table $D$ gives a complete instance $v(D)$. Under the
closed-world semantics the possible worlds of $D$ are $[\![D]\!] = \{v(D) : v \text{ a valuation}\}$. The
certain answers of a query $q$ on $D$ are $\bigcap_{I \in [\![D]\!]} q(I)$, a set of null-free tuples. A
Codd table is a naive table in which every null occurs at most once.

## Depends on

- [Tuple](../relational-algebra/tuple.md)
- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)

## Sources

- Incomplete Information in Relational Databases (Imielinski, Lipski), JACM 1984 — JACM 31(4) 1984, Section 1, pp. 762–763 (Codd tables and V-tables with marked nulls). <https://cs.uwaterloo.ca/~david/kbdb/imielinskilipski.pdf>
- SQL's Three-Valued Logic and Certain Answers (Libkin), ACM TODS 2016 — ACM TODS 41(1) 2016, author copy, Section 1, equation (3), and Section 2, "Homomorphisms, valuations, and semantics" (valuations fix constants; closed-world semantics $[\![D]\!]$). <https://homepages.inf.ed.ac.uk/libkin/papers/tods16.pdf>
