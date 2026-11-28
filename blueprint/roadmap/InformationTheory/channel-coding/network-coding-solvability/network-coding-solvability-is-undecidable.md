# Solvability of network coding is undecidable

No algorithm decides whether a network, with given source messages available at and demanded by its nodes, admits a coding scheme over some finite alphabet; consequently the alphabet size a solvable network may need is not bounded by any computable function.

**Networks (Li, following Dougherty, Freiling and Zeger).** A *network* is a finite acyclic [directed multigraph](../../../Biology/bioinformatics/omnitigs-and-safe-walks-in-genome-assembly/multigraph.md) $(\mathcal{N}, \mathcal{L})$ with source messages $M_1, \dots, M_n$; each node $v$ has access to the messages with indices in a set $\mathcal{C}_v \subseteq \{1, \dots, n\}$ and demands those with indices in $\mathcal{D}_v$. For an alphabet size $q \ge 2$, the messages are independent and uniformly distributed on sets of size $q$, and each edge $f$ carries a signal $X_f$ taking at most $q$ values. Writing $Y \le_\iota X$ when $Y$ is a function of $X$, the *coding constraint* is that, for every node $v$, the demanded messages and the signals on the outgoing edges of $v$ are functions of the accessible messages and the signals on the incoming edges:

$$
\bigl(M_{\mathcal{D}_v}, X_{\mathrm{out}(v)}\bigr) \le_\iota \bigl(M_{\mathcal{C}_v}, X_{\mathrm{in}(v)}\bigr).
$$

The network is *solvable* if for some $q \ge 2$ there are such messages and signals satisfying every coding constraint.

**Theorem (Li).** It is undecidable, given a network, whether it is solvable (Theorem 22 of the source).

The source also proves that for every fixed $c \ge 2$ it is undecidable, given a network, whether it is solvable with alphabet size $q = c^m$ for some $m \ge 1$, that is, with messages and signals that are blocks of symbols from an alphabet of size $c$ (Theorem 23). Writing $q_{\max}(m)$ for the largest minimum alphabet size of a solvable network with at most $m$ nodes, $m$ edges and $m$ source messages, there is no computable function $f$ with $q_{\max}(m) = O(f(m))$ (Corollary 30). Network coding for multiple unicast networks, and index coding, are undecidable as well, through known reductions to them. Earlier, Kühne and Yashfe proved that the existence of a vector linear network code is undecidable.

## Depends on

- [Directed multigraph](../../../Biology/bioinformatics/omnitigs-and-safe-walks-in-genome-assembly/multigraph.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the uniform word problem for finite groups, which is undecidable by a theorem of Slobodskoi. A network of Dougherty, Freiling and Zeger forces its signals to carry the structure of an abelian group, finite groups are embedded in the automorphism group of an abelian group through their left regular representation, and subnetworks enforce the action of each automorphism, so that the network is solvable exactly when the given relations fail to imply the given equation in some finite group. Corollary 30 follows from Theorem 22 by the observation of Rasala Lehman that a computable bound on the alphabet size would give a decision procedure by exhaustive search. A good expansion links pages for Slobodskoi's undecidability of the uniform word problem for finite groups and for the network constructions.

## Sources

- C. T. Li, "Undecidability of network coding, conditional information inequalities, and conditional independence implication", IEEE Transactions on Information Theory 69 (2023), no. 6, 3493–3510, https://doi.org/10.1109/TIT.2023.3247570; read in arXiv:2205.11461v3 (Section IV, Theorems 22 and 23 and Corollary 30, and the introduction of arXiv:2205.11461v3).
