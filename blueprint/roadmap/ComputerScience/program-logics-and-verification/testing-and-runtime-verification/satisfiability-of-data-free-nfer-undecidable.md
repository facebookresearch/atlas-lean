# Satisfiability of data-free nfer specifications is undecidable

Nfer is a rule language for runtime verification that builds named intervals from timestamped events. Even without data, it is undecidable whether some event trace makes a specification produce an interval with a given name.

**Setting (Kauffman, Larsen and Zimmermann).** Fix finite alphabets $\Sigma \subseteq \mathcal{I}$ of event and interval identifiers. An *event* is a pair $(\eta, t)$ with $\eta \in \Sigma$ and $t \in \mathbb{N}$; a *trace* is a finite sequence of events with nondecreasing timestamps. An *interval* is a triple $(\eta, s, e)$ with $\eta \in \mathcal{I}$ and $s \le e$ in $\mathbb{N}$, and a *pool* is a set of intervals. A data-free nfer *specification* is a finite list of rules. An *inclusive rule* $\eta \leftarrow \eta_1 \oplus \eta_2$, with $\oplus$ one of the clock predicates $\mathsf{before}$, $\mathsf{meet}$, $\mathsf{during}$, $\mathsf{coincide}$, $\mathsf{start}$, $\mathsf{finish}$, $\mathsf{overlap}$, $\mathsf{slice}$, produces an $\eta$-labeled interval whenever two intervals labeled $\eta_1$ and $\eta_2$ satisfy the corresponding Allen relation, with timestamps taken from them (for example, $\mathsf{meet}$ requires the first to end where the second starts and produces the interval from the start of the first to the end of the second). An *exclusive rule* $\eta \leftarrow \eta_1 \;\mathsf{unless}\; \ominus\; \eta_2$, with $\ominus \in \{\mathsf{after}, \mathsf{follow}, \mathsf{contain}\}$, copies an $\eta_1$-labeled interval as an $\eta$-labeled one when no other $\eta_2$-labeled interval stands in the relation $\ominus$ to it. A trace is turned into the pool of zero-length intervals $(\eta, t, t)$; rules are evaluated in topological order of their strongly connected dependency components, iterating cycles to a fixed point, and exclusive rules may not occur in cycles. The *satisfiability problem* asks, given a specification, a set $\Sigma' \subseteq \Sigma$ of input identifiers and a target identifier $\eta_T$, whether some nonempty trace with identifiers in $\Sigma'$ makes the specification produce an $\eta_T$-labeled interval.

**Theorem (Kauffman, Larsen and Zimmermann).** The satisfiability problem for data-free nfer is undecidable.

The same paper shows that satisfiability is decidable for cycle-free specifications, with a NEXPTIME lower bound, and in polynomial time for specifications with inclusive rules only.

## Depends on

None.

## Proof depends on

- [PCP many-one reduces to nonemptiness of the intersection of two context-free languages](../../../TheoryOfComputation/undecidable-problems/intersection-problem-for-context-free-languages/many-one-reducible-pcp-inter.md)
- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Chomsky normal form theorem](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/chomsky-normal-form/exists-chomsky-normal-form.md)

## Expansion

The proof reduces nonemptiness of the intersection of two context-free languages. Exclusive rules first discard events whose timestamps are shared with differently named events and then cut the trace into minimal contiguous intervals labeled by their starting events, so that the remaining intervals spell a word in order. For grammars in Chomsky normal form, recursive inclusive rules then label an interval by each nonterminal that derives the corresponding factor of that word, and a final rule produces a target interval when the start symbols of two grammars $G_1$ and $G_2$ label the same interval. So the specification is satisfiable exactly when $L(G_1) \cap L(G_2)$ is nonempty.

## Sources

- Sean Kauffman, Kim Guldstrand Larsen and Martin Zimmermann, *The Complexity of Data-Free Nfer*, Runtime Verification (RV 2024), Lecture Notes in Computer Science 15191, Springer, 2024, pp. 174–191, https://doi.org/10.1007/978-3-031-74234-7_11; the syntax and semantics of data-free nfer, the satisfiability problem and the undecidability theorem, read in arXiv:2407.03155v4.
