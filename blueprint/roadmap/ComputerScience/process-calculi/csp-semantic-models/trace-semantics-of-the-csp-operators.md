# Trace semantics of the CSP operators

The [traces model](the-traces-model.md) gives each CSP operator a clause computing the traces of a compound process from those of its parts. Writing $\langle\rangle$ for the empty trace, $\langle a \rangle ^\frown s$ for the trace starting with $a$, and $\Sigma^{*\checkmark}$ for the traces that may end with $\checkmark$:

- $\mathrm{traces}(STOP) = \{\langle\rangle\}$ and $\mathrm{traces}(SKIP) = \{\langle\rangle, \langle \checkmark \rangle\}$;
- $\mathrm{traces}(a \to P) = \{\langle\rangle\} \cup \{\langle a \rangle ^\frown s \mid s \in \mathrm{traces}(P)\}$, and $\mathrm{traces}(?x : A \to P) = \{\langle\rangle\} \cup \{\langle a \rangle ^\frown s \mid a \in A,\ s \in \mathrm{traces}(P[a/x])\}$;
- $\mathrm{traces}(P \sqcap Q) = \mathrm{traces}(P \mathbin{\Box} Q) = \mathrm{traces}(P) \cup \mathrm{traces}(Q)$, and $\mathrm{traces}(\sqcap S) = \bigcup \{\mathrm{traces}(P) \mid P \in S\}$ for a nonempty set $S$ of processes;
- $\mathrm{traces}(P \parallel_X Q) = \bigcup \{ s \parallel_X t \mid s \in \mathrm{traces}(P),\ t \in \mathrm{traces}(Q)\}$, where $s \parallel_X t$ is the set of traces obtained by interleaving $s$ and $t$ while synchronizing on the events of $X$ and on $\checkmark$;
- $\mathrm{traces}(P \setminus X) = \{ s \setminus X \mid s \in \mathrm{traces}(P)\}$, where $s \setminus X$ deletes the events of $X$ from $s$;
- $\mathrm{traces}(P[\![R]\!])$ is the set of traces $\langle b_1, \dots, b_n \rangle$ and $\langle b_1, \dots, b_n, \checkmark \rangle$ such that $\langle a_1, \dots, a_n \rangle$, respectively $\langle a_1, \dots, a_n, \checkmark \rangle$, is a trace of $P$ with $a_i \mathrel{R} b_i$ (that is, related pointwise by $R^\checkmark = R \cup \{(\checkmark, \checkmark)\}$) for every $i$;
- $\mathrm{traces}(P ; Q) = (\mathrm{traces}(P) \cap \Sigma^*) \cup \{ s ^\frown t \mid s ^\frown \langle \checkmark \rangle \in \mathrm{traces}(P),\ t \in \mathrm{traces}(Q)\}$.

A recursion $\mu p . F(p)$ denotes the $\subseteq$-least fixed point of $F$ over $\mathcal{T}$, which is the union of the trace sets of $F^n(STOP)$ for $n \in \mathbb{N}$. Every clause other than recursion is the lifting of a family of relations on traces.

## Depends on

- [The traces model of CSP](the-traces-model.md)
- [The operational semantics of CSP](csp-operational-semantics.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 1.3.1 (the traces of $STOP$, prefixing, prefix choice and the choice operators), Section 6.4 (traces over $\Sigma^{*\checkmark}$, $SKIP$, sequential composition and renaming with $\checkmark$, pp. 147–148), and Section 8.2: the relational representation of sequential composition and of the other operators (pp. 186–187) and the choice of the $\subseteq$-least fixed point for recursion (pp. 193–194).
- A. W. Roscoe, *The Theory and Practice of Concurrency*, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.3.2, p. 205 (the renaming relation extended so that $\checkmark$ is related to $\checkmark$).
