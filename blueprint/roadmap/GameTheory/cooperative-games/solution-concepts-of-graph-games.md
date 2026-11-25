# Solution concepts of graph games (Deng-Papadimitriou)

Let $G$ be a finite undirected graph without loops, with real edge weights (possibly negative), and let the cooperative game on its vertex
set be $v_G(S) =$ the total weight of the edges with both endpoints in $S$. Then the Shapley value of vertex $i$ is half the total weight of
the edges incident to $i$; and the following are equivalent: the core of $v_G$ is nonempty; $G$ has no negative cut (no vertex set $S$ for which
the total weight of edges between $S$ and its complement is negative); the Shapley value lies in the core. The source takes integer weights;
the statement and its proof hold verbatim for real weights. The NP-completeness of deciding whether a negative cut exists is cited, not part of
this statement.

## Depends on

- [Cooperative game with transferable utility](shapley-value/coop-game.md)
- [Core allocation](bondareva-shapley-theorem/is-core-allocation.md)
- [Shapley's formula](shapley-value/shapley-formula.md)

## Related topics

- [Efficient value](shapley-value/is-efficient.md)
- [Bondareva–Shapley theorem](bondareva-shapley-theorem/bondareva-shapley.md)

## Sources

- X. Deng and C. H. Papadimitriou, *On the Complexity of Cooperative Solution Concepts*, Math. Oper. Res. 19(2) (1994), 257–266, §1 (the graph game), Theorem 1 (the Shapley value) and Lemmas 1 and 2 (the core), pp. 258–260; Lemma 3 is the NP-completeness of the negative-cut question. <https://yhwu-is.github.io/Teach/ec/seminar/25sp/On%20the%20Complexity%20of%20Cooperative%20Solution%20Concepts.pdf>
