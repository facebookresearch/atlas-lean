# Datalog on K-relations over ω-continuous semirings

A commutative semiring $(K, +, \cdot, 0, 1)$ is naturally ordered when $a \le b \iff \exists x\, (a + x = b)$ is a
partial order, $\omega$-complete when moreover every chain $a_0 \le a_1 \le \cdots$ has a least upper bound (so a
countable sum $\sum_n a_n$ is the supremum of its finite partial sums), and $\omega$-continuous when $+$ and $\cdot$
preserve these suprema in each argument. Examples are $\mathbb B$, $\mathbb N^\infty = \mathbb N \cup \{\infty\}$, the
tropical semiring $(\mathbb N^\infty, \min, +, \infty, 0)$ and $([0, 1], \max, \min, 0, 1)$; $\mathbb N$ and
$\mathbb N[X]$ are not $\omega$-complete.

For a commutative $\omega$-continuous semiring $K$, a Datalog query $q$ whose rule bodies are relational atoms, and an
input $K$-relation $R$ over its extensional relation names, the output assigns to each tuple $t$

$$q(R)(t) = \sum_{\tau \text{ a derivation tree of } t} \ \prod_{t' \in \mathrm{leaves}(\tau)} R(t'),$$

where derivation trees are the proof trees of $t$ from the rules of $q$ with input tuples at the leaves (a leaf tuple
counted once per leaf occurrence). The result has finite support. For $K = \mathbb B$ this is the usual Datalog
semantics, and on nonrecursive queries obtained from positive relational algebra with equality selections it agrees
with the $K$-relation semantics of that algebra.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)
- [Datalog programs and the immediate consequence operator](../datalog/datalog-programs-and-the-immediate-consequence-operator.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Section 5: the definitions of naturally ordered, $\omega$-complete and $\omega$-continuous semirings, Definition 5.1, Propositions 5.2 and 5.3. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
