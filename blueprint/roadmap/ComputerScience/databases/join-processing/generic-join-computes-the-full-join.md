# Generic-Join computes the full join

For a full natural-join query $Q = \Join_{e \in E} R_e$ over a finite hypergraph $(V, E)$ whose edges are nonempty and cover $V$, and finite
relations $R_e$ over attribute sets $e$, write $E_I = \{e \in E : e \cap I \neq \varnothing\}$ for $I \subseteq V$. The recursive Generic-Join
algorithm (for $|V| = 1$ return $\bigcap_{e \in E} R_e$; otherwise partition $V = I \cup J$ with $1 \le |I| < |V|$, compute
$L = \text{Generic-Join}(\Join_{e \in E_I} \pi_{I \cap e} R_e)$ and, for every $t_I \in L$,
$Q[t_I] = \text{Generic-Join}(\Join_{e \in E_J} \pi_{J \cap e}(R_e \ltimes t_I))$, and return $\bigcup_{t_I \in L} \{t_I\} \times Q[t_I]$) returns exactly the set of
tuples $t$ over $V$ with $\pi_e t \in R_e$ for every $e$, each once. The restriction to $E_I$ and $E_J$ is needed: an edge disjoint from $I$ would
enter the recursive call as a relation with no attributes.

## Proof

Induction on $|V|$. For $|V| = 1$ the claim is the definition of the join. Otherwise, a tuple $t$ is in $Q$ iff $t_I = \pi_I t$ lies in the projected join
(which contains $\pi_I Q$; extra tuples of $L$ give empty $Q[t_I]$) and $\pi_J t$ lies in the join of the relations restricted to $t_I$: an edge
inside $I$ is checked by $L$, an edge inside $J$ by $Q[t_I]$, and an edge meeting both by $\pi_{J \cap e}(R_e \ltimes t_I)$; this is the decomposition
$Q = \bigcup_{t_I \in L} \{t_I\} \times Q[t_I]$. The union is disjoint because the $t_I$ are distinct, so no tuple is output twice.

## Depends on

- [Natural join queries, their hypergraphs and fractional edge covers](natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)

## Sources

- H. Q. Ngo, C. Ré and A. Rudra, *Skew strikes back: new developments in the theory of join algorithms*, SIGMOD Record 42(4) (2013); arXiv:1310.3314, Section 4, the notation $E_I$ before Lemma 4.1, decomposition (11) and Algorithm 3 (Generic-Join). <https://arxiv.org/abs/1310.3314>
