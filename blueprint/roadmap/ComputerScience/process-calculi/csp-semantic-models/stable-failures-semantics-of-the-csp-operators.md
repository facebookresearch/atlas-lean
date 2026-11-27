# Stable failures semantics of the CSP operators

In the [stable failures model](the-stable-failures-model.md) a process is the pair $(\mathrm{traces}(P), \mathrm{failures}(P))$. The traces component of each operator is computed by its clause in the [trace semantics](trace-semantics-of-the-csp-operators.md), and the failures component as follows, with $\Sigma^\checkmark = \Sigma \cup \{\checkmark\}$:

- $\mathrm{failures}(STOP) = \{(\langle\rangle, X) \mid X \subseteq \Sigma^\checkmark\}$ and $\mathrm{failures}(SKIP) = \{(\langle\rangle, X) \mid X \subseteq \Sigma\} \cup \{(\langle \checkmark \rangle, X) \mid X \subseteq \Sigma^\checkmark\}$;
- $\mathrm{failures}(a \to P) = \{(\langle\rangle, X) \mid a \notin X\} \cup \{(\langle a \rangle ^\frown s, X) \mid (s, X) \in \mathrm{failures}(P)\}$, and $\mathrm{failures}(?x : A \to P) = \{(\langle\rangle, X) \mid X \cap A = \emptyset\} \cup \{(\langle a \rangle ^\frown s, X) \mid a \in A,\ (s, X) \in \mathrm{failures}(P[a/x])\}$;
- $\mathrm{failures}(P \sqcap Q) = \mathrm{failures}(P) \cup \mathrm{failures}(Q)$, and $\mathrm{failures}(\sqcap S) = \bigcup \{\mathrm{failures}(P) \mid P \in S\}$ for a nonempty set $S$;
- $\mathrm{failures}(P \mathbin{\Box} Q) = \{(\langle\rangle, X) \mid (\langle\rangle, X) \in \mathrm{failures}(P) \cap \mathrm{failures}(Q)\} \cup \{(s, X) \mid (s, X) \in \mathrm{failures}(P) \cup \mathrm{failures}(Q),\ s \ne \langle\rangle\} \cup \{(\langle\rangle, X) \mid X \subseteq \Sigma,\ \langle \checkmark \rangle \in \mathrm{traces}(P) \cup \mathrm{traces}(Q)\}$;
- $\mathrm{failures}(P \parallel_X Q) = \{(u, Y \cup Z) \mid Y \setminus (X \cup \{\checkmark\}) = Z \setminus (X \cup \{\checkmark\}),\ (s, Y) \in \mathrm{failures}(P),\ (t, Z) \in \mathrm{failures}(Q),\ u \in s \parallel_X t\}$;
- $\mathrm{failures}(P \setminus X) = \{(s \setminus X, Y) \mid (s, Y \cup X) \in \mathrm{failures}(P)\}$;
- $\mathrm{failures}(P[\![R]\!]) = \{(s', X) \mid \exists s.\ s \mathrel{R^\checkmark} s' \wedge (s, (R^\checkmark)^{-1}(X)) \in \mathrm{failures}(P)\}$, where $R^\checkmark = R \cup \{(\checkmark, \checkmark)\}$, extended to traces pointwise, and $(R^\checkmark)^{-1}(X) = \{a \mid \exists b \in X.\ a \mathrel{R^\checkmark} b\}$; without the pair $(\checkmark, \checkmark)$ the identity renaming of $SKIP$ would gain the initial failure $(\langle\rangle, \{\checkmark\})$;
- $\mathrm{failures}(P ; Q) = \{(s, X) \mid s \in \Sigma^*,\ (s, X \cup \{\checkmark\}) \in \mathrm{failures}(P)\} \cup \{(s ^\frown t, X) \mid s ^\frown \langle \checkmark \rangle \in \mathrm{traces}(P),\ (t, X) \in \mathrm{failures}(Q)\}$.

A recursion denotes the least fixed point with respect to componentwise $\subseteq$, the reverse of refinement in $\mathcal{F}$. Unlike the failures-divergences semantics, no clause infers divergence, so hiding needs no special treatment.

## Depends on

- [The stable failures model of CSP](the-stable-failures-model.md)
- [Trace semantics of the CSP operators](trace-semantics-of-the-csp-operators.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.4: the observation that the traces component uses the clauses of $\mathcal{T}$ and that recursion takes fixed points with respect to $\subseteq$ (p. 213), and the failures clauses for every operator (p. 214).
- A. W. Roscoe, *The Theory and Practice of Concurrency*, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.3.2, p. 205 (the renaming relation extended so that $\checkmark$ is related to $\checkmark$).
