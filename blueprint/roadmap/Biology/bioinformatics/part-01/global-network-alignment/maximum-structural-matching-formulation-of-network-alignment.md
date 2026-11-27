# Maximum structural matching formulation of network alignment

**Definitions.** Let $G_1 = (V_1,E_1)$ and $G_2 = (V_2,E_2)$ be networks. A network alignment is a map $a : V_1 \to V_2 \cup \{-\}$ that is injective on the vertices it does not send to the gap symbol $-$. Let $D(a) = \{i \in V_1 : a(i) \neq -\}$. Node scores are $\sigma : V_1 \times V_2 \to \mathbb R_{\ge 0}$, and pair scores $\tau : V_1 \times V_2 \times V_1 \times V_2 \to \mathbb R_{\ge 0}$ are symmetric, $\tau(i,j,k,l) = \tau(k,l,i,j)$. The score of $a$ counts each unordered pair of distinct aligned vertices once:

$$s(a) = \sum_{i \in D(a)} \sigma(i,a(i)) + \sum_{\{i,k\} \subseteq D(a),\ i \neq k} \tau(i,a(i),k,a(k)).$$

The pairwise global network alignment problem asks for an alignment of maximum score.

The alignment graph $A$ is the complete bipartite graph on $V_1 \cup V_2$ with edge weights $w(i,j) = \sigma(i,j)$. A structural match is an unordered pair $\{(i,j),(k,l)\}$ of distinct alignment edges, with weight $\tau(i,j,k,l)$. The structural score of a matching $M$ of $A$ is, with the same convention,

$$s(M) = \sum_{(i,j)\in M} \sigma(i,j) + \sum_{\{(i,j),(k,l)\} \subseteq M,\ (i,j) \neq (k,l)} \tau(i,j,k,l).$$

**Theorem.**
1. Pairwise global network alignment is NP-hard.
2. Network alignments correspond one-to-one to matchings in $A$, by $a \mapsto M_a = \{(i,a(i)) : i \in D(a)\}$, and $s(a) = s(M_a)$. So the problem is the maximum structural matching problem.
3. Let $P$ be the set of unordered pairs of distinct alignment edges. With binary variables $x_{ij}$ for alignment edges and $y_{ijkl}$ for $\{(i,j),(k,l)\} \in P$, the maximum score equals the optimal value of the integer linear program

$$\max \sum_{(i,j)} \sigma(i,j)\,x_{ij} + \sum_{\{(i,j),(k,l)\} \in P} \tau(i,j,k,l)\,y_{ijkl}$$

subject to $\sum_{(i,j)\in\delta(v)} x_{ij} \le 1$ for all $v \in V_1 \cup V_2$, $y_{ijkl} \le x_{ij}$, $y_{ijkl} \le x_{kl}$, and $x, y \in \{0,1\}$. A feasible point has objective at most $s(M)$ for the matching $M$ with characteristic vector $x$, with equality when $y_{ijkl} = x_{ij}x_{kl}$ for every pair.

## Expansion

NP-hardness is by reduction from maximum common subgraph: with $\sigma \equiv 0$ and $\tau(i,j,k,l) = 1$ exactly when $(i,k) \in E_1$ and $(j,l) \in E_2$, an optimal alignment maps the largest set of edges of $G_1$ onto edges of $G_2$. The matching correspondence holds because an alignment, ignoring order, is exactly a set of vertex pairs no two of which share an endpoint. The degree constraints encode the matching polytope's inequalities, and the $y$ constraints are the standard linearization of the quadratic objective: they force $y_{ijkl} \le x_{ij}x_{kl}$, and since $\tau \ge 0$ an optimal point may take $y_{ijkl} = x_{ij}x_{kl}$. Each structural match appears in exactly one term of $s(a)$, $s(M_a)$ and the objective, so the three scores agree.

## Sources

- G. W. Klau, "A new graph-based method for pairwise global network alignment", BMC Bioinformatics 10(Suppl 1):S59 (2009), Definitions 1–6, Theorem 1, Observation 1, Lemma 1 and ILP (4)–(9), <https://doi.org/10.1186/1471-2105-10-S1-S59>, PMCID PMC2648773.
