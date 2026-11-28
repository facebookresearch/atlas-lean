# Reachability in acyclic Petri nets with resets is undecidable

Reachability stays undecidable for Petri nets with reset edges whose underlying net of places, transitions and arcs is acyclic, although coverability for them is PSPACE-complete and acyclic workflow nets with resets have PSPACE-complete reachability.

**Setting (Chistikov, Czerwiński, Hofman, Mazowiecki and Sinclair-Banks).** A [Petri net](../../../place-transition-petri-nets.md) with resets is $(P, T, F, R)$ where $(P, T, F)$ is a Petri net and $R : T \to 2^P$ gives for each transition $t$ the set of places it resets. Firing $t$ at a marking $\vec m \in \mathbb N^P$ requires $\vec m[p] \ge F(p, t)$ for every place $p$; it first consumes $F(p, t)$ tokens from each $p$, then sets every place of $R(t)$ to $0$, then produces $F(t, q)$ tokens in each place $q$. Whether a reset place holds tokens does not affect whether $t$ can fire. The net is *acyclic* if the directed graph of places and transitions with the arcs of $F$ is acyclic; reset edges are not subject to this restriction. The *reachability problem* asks, given a net, an initial marking $\vec m$ and a target marking $\vec n$, whether some firing sequence leads from $\vec m$ to $\vec n$.

**Theorem (Chistikov, Czerwiński, Hofman, Mazowiecki and Sinclair-Banks).** Reachability in acyclic Petri nets with resets is undecidable.

The same paper shows that coverability in acyclic Petri nets with resets, and both coverability and reachability in acyclic workflow nets with resets, are PSPACE-complete. Without acyclicity, reachability in Petri nets with resets is undecidable by a result of Araki and Kasami.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from reachability in Petri nets with zero tests, which is undecidable because they simulate counter machines. First, an arbitrary Petri net with zero tests is simulated by an acyclic one with zero tests: each transition $t$ is replaced by three transitions that choose $t$, perform its consumption and zero tests, and perform its production, using two control places per transition and zero tests on all control places so that simulations of different transitions do not interleave; the arcs then form an acyclic graph. Second, zero tests are simulated by resets: every place $p$ gets a copy $c_p$ that receives the same arcs but is never reset, and a zero test on $p$ becomes a reset of $p$; the initial and target markings give $c_p$ as many tokens as $p$. Resetting a nonempty place makes $p$ and $c_p$ differ for the rest of the run, so the target is reachable only if every simulated zero test was faithful. Both steps preserve acyclicity and take logarithmic space.

## Sources

- Dmitry Chistikov, Wojciech Czerwiński, Piotr Hofman, Filip Mazowiecki and Henry Sinclair-Banks, "Acyclic Petri and Workflow Nets with Resets", in *43rd IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2023)*, Leibniz International Proceedings in Informatics 284, Schloss Dagstuhl, 2023, pp. 16:1–16:18, doi:[10.4230/LIPIcs.FSTTCS.2023.16](https://doi.org/10.4230/LIPIcs.FSTTCS.2023.16); read in arXiv:2310.01992v2 ([arXiv](https://arxiv.org/abs/2310.01992v2)), whose numbering is used: Section 2 (Petri nets with resets, acyclicity, the reachability and coverability problems), Theorem 4.13 with its proof in Subsection 4.2 ("Reachability in Acyclic Petri Nets with Resets", Lemmas 4.14 and 4.15), and the summary of results in Section 1 (Figure 2).
