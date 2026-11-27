# Constant amortized random-walk insertion time below the peeling threshold

For every $d \ge 3$ and every fixed load factor $c < c_d^{\Delta}$, let $n = cm$ keys be inserted one after another into an initially empty $d$-ary cuckoo table with $m$ slots by the walk without immediate return (variant (b) of random-walk insertion: the new key takes a uniform one of its $d$ candidates without inspecting the others, and an evicted key a uniform one of its other $d - 1$ candidates); Walzer checks that the argument also covers the uniform walk (a). There is an event $E$ of probability $1 - o(1)$ over the hash functions such that the expected total number of steps for all $n$ insertions, conditioned on $E$, is $O(n)$, with a constant depending only on $c$ and $d$. Hence the expected amortized insertion time is $O(1)$. This bounds the total work, not the expected time of each particular insertion.

## Proof sketch

Below the peeling threshold the hashing hypergraph, with slots as vertices and keys as hyperedges, peels completely; fix a peeling $F$, which orients each key $e$ to a slot $F(e)$. Key $e$ *directly depends* on key $e'$ when $F(e) \in e'$, and $D_F(e)$ is the multiset of such $e'$, each counted with the multiplicity with which $e'$ contains $F(e)$. Walzer's peeling number (Section 3, equation (2)) is defined recursively by

$$
\mathrm{peel}_F(e) = \sum_{e' \in D_F(e)} \bigl(1 + \mathrm{peel}_F(e')\bigr),
$$

with $\mathrm{peel}_F(e) = 0$ when $D_F(e) = \emptyset$. It counts the non-trivial dependency paths starting at $e$ with multiplicity, not the round or depth at which $e$ is peeled: two direct predecessors of peeling number zero already give $\mathrm{peel}_F(e) = 2$. Walzer couples the successive walks with a random eviction process with target orientation $F$ and shows (Lemma 4) that its expected number of rounds is at most $d\,\bigl(n + \sum_e \mathrm{peel}_F(e)\bigr)$. For a random peeling $F$, Proposition 5 gives a high-probability event $E$ with $\mathbb{E}\bigl[\sum_e \mathrm{peel}_F(e) \mid E\bigr] = O(m)$, hence $O(n)$ total work at fixed $c$. The argument bounds total work and gives no tail bound for a walk started at a given slot.

## Depends on

- [Peeling threshold of random hypergraphs](peeling-threshold.md)
- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)
- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Sources

- Stefan Walzer, "Insertion Time of Random Walk Cuckoo Hashing below the Peeling Threshold", ESA (2022), arXiv:2202.05546.
