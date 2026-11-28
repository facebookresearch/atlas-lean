# The ALLDIFFERENT constraint and its value graph

ALLDIFFERENT requires its variables to take pairwise different values. Its value graph joins each variable to the values in its domain, and an assignment satisfying the constraint is the same thing as a matching of the value graph that covers every variable.

Let $X_C=(x_1,\dots,x_p)$, $p\ge1$, be distinct variables with finite domains $D_1,\dots,D_p$, all contained in a fixed finite set $V$ of values (for example the union of the initial domains; values of $V$ in no current domain are allowed).

- The constraint $\mathrm{ALLDIFFERENT}(x_1,\dots,x_p)$ allows exactly the tuples $(d_1,\dots,d_p)\in D_1\times\dots\times D_p$ with $d_u\ne d_v$ for all $u\ne v$ (Régin's *constraint of difference*).
- Its **value graph** is the bipartite graph $GV(C)$ with vertex classes $X_C$ and $V$ (disjoint copies) and an edge $(x_i,a)$ iff $a\in D_i$. Régin takes $V=D_1\cup\dots\cup D_p$; values outside every domain are isolated vertices and change nothing below.
- A [matching](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/is-matching.md) $M$ (no two edges share a vertex) **covers** $X_C$ when every $x_i$ is an endpoint of an edge of $M$. A matching covering $X_C$ is a maximum matching of $GV(C)$, since no matching has more than $p$ edges.

The map sending an allowed tuple $(d_1,\dots,d_p)$ to the edge set $\{(x_i,d_i)\}$ is a bijection between allowed tuples and matchings of $GV(C)$ that cover $X_C$. In particular the constraint has an allowed tuple iff a maximum matching of $GV(C)$ has $p$ edges; an empty domain makes it unsatisfiable. Conversely, every finite bipartite graph with classes $L=\{1,\dots,p\}$ and $R$ is the value graph, over $V=R$, of the ALLDIFFERENT constraint with $D_i$ the set of neighbours of $i$; when $|R|=p$, the matchings covering the variables are exactly the perfect matchings of the graph.

## Depends on

- [Matching in a bipartite graph](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/is-matching.md): matchings of the value graph.

## Proof depends on

None.

## Expansion

An allowed tuple gives one edge per variable, and distinct variables receive distinct values, so the edges have distinct endpoints on both sides; conversely a covering matching assigns each variable a value of its domain, with no value used twice. Both maps are inverse to each other. The converse remark is immediate from the definition with the fixed value set $V=R$, which keeps isolated vertices of $R$; with Régin's choice $V=D_1\cup\dots\cup D_p$, isolated right vertices would be dropped and a balanced graph would no longer be literally a value graph. Bessiere, Katsirelos, Narodytska and Walsh use the remark, with all initial domains equal to $\{1,\dots,p\}$, to transfer monotone circuit lower bounds for perfect matching to ALLDIFFERENT.

## Sources

- J.-C. Régin, "A filtering algorithm for constraints of difference in CSPs", *Proceedings of the Twelfth National Conference on Artificial Intelligence (AAAI-94)*, AAAI Press (1994), 362–367, [https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/](https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/). Definition 2 (constraint of difference), Definition 4 (value graph), Definition 5 (matching, covering) and the proof of Theorem 1, pp. 363–364.
- W.-J. van Hoeve and I. Katriel, "Global constraints", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 6, 169–208, doi:10.1016/S1574-6526(06)80010-6; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf). Definition 1 (alldifferent), Definition 7 (value graph), Theorem 4 and Corollary 5 (Régin), §§7.2.3 and 7.3.1 (section and theorem numbers of the author copy).
- C. Bessiere, G. Katsirelos, N. Narodytska and T. Walsh, "Circuit complexity and decompositions of global constraints", *Proceedings of the Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 2009)*, 412–417, [https://www.ijcai.org/proceedings/2009/76](https://www.ijcai.org/proceedings/2009/76). Proof of Corollary 4 (every bipartite graph is a value graph), arXiv:0905.3757v1, [https://arxiv.org/abs/0905.3757v1](https://arxiv.org/abs/0905.3757v1).
