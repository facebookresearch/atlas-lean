# Parameterized model checking of direction-aware token-passing systems is undecidable

Token-passing systems run copies of one finite-state process on the vertices of a graph and pass a single valueless token along its edges. If processes may choose the directions in which they send and receive the token, verifying a 1-indexed universal LTL property for every bi-directional ring is undecidable, and for some families of graphs undecidability already holds without direction awareness.

**Setting (Aminof, Jacobs, Khalimov and Rubin).** A *process template* $P$ is a finite labeled transition system whose states are partitioned into states with and without the token, with two initial states, internal actions that keep token ownership, actions $\mathsf{snd}$ that give up the token and actions $\mathsf{rcv}$ that take it, no deadlocks, and $\mathsf{snd}$ and $\mathsf{rcv}$ alternating along every infinite run. A *topology* $G = (V, E, x)$ is a finite directed graph without self-loops with an initial vertex $x$. The *token-passing system* $P^G$ places a copy of $P$ at each vertex, starts with the token at $x$, and lets either one process take an internal step or two processes $v$, $w$ with $(v, w) \in E$ pass the token by synchronizing $\mathsf{snd}$ at $v$ with $\mathsf{rcv}$ at $w$. In a *direction-aware* system, edges also carry sending and receiving directions, and processes send and receive along chosen directions; $\mathcal{P}_{\mathsf{sndrcv}}$ (respectively $\mathcal{P}_{\mathsf{snd}}$, $\mathcal{P}_{\mathsf{rcv}}$) is the class of templates that choose both directions (respectively only sending, only receiving directions). Indexed formulas also allow guarded index quantifiers $\forall x.\, x \in Y \to \varphi$, $\exists x.\, x \in Y \wedge \varphi$ over vertices designated by a set $Y$ of index variables and $\forall x.\, x \in E(y) \to \varphi$, $\exists x.\, x \in E(y) \wedge \varphi$ over the successors of the vertex of $y$ (Section 2.3). *Prenex indexed* formulas are $Q_1 x_1 \dots Q_k x_k\, \varphi$ with index quantifiers over vertices and $\varphi$ a formula of LTL or CTL without the next-time operator over atoms indexed by $x_1, \dots, x_k$; $\{\forall\}^k$-$\mathrm{LTL}\backslash\mathrm{X}$ and $\{\exists\}^k$-$\mathrm{CTL}\backslash\mathrm{X}$ restrict to $k$ universal or $k$ existential quantifiers, and $\forall$-$\mathrm{LTL}\backslash\mathrm{X}$ is the case $k = 1$. For a set $\mathcal{G}$ of topologies, the *parameterized model checking problem* $\mathrm{PMCP}_{\mathcal{G}}(\mathcal{P}, \mathcal{F})$ asks, given $P \in \mathcal{P}$ and $\varphi \in \mathcal{F}$, whether $P^G \models \varphi$ for every $G \in \mathcal{G}$.

**Theorem (Aminof, Jacobs, Khalimov and Rubin).** Let $\mathcal{B}$ be the set of bi-directional rings with directions clockwise and counter-clockwise.

1. $\mathrm{PMCP}_{\mathcal{B}}(\mathcal{P}_{\mathsf{sndrcv}}, \forall\text{-}\mathrm{LTL}\backslash\mathrm{X})$ is undecidable.
2. For $\mathcal{F}$ equal to $\{\forall\}^9$-$\mathrm{LTL}\backslash\mathrm{X}$ or $\{\exists\}^9$-$\mathrm{CTL}\backslash\mathrm{X}$ and $\mathcal{P}$ equal to $\mathcal{P}_{\mathsf{snd}}$ or $\mathcal{P}_{\mathsf{rcv}}$, there is a set of topologies $\mathcal{G}$ for which $\mathrm{PMCP}_{\mathcal{G}}(\mathcal{P}, \mathcal{F})$ is undecidable.
3. There are a single direction-unaware process template $P$ and computable sets of topologies $\mathcal{G}$, $\mathcal{H}$ such that $\mathrm{PMCP}_{\mathcal{G}}(\{P\}, \cdot)$ restricted to prenex indexed LTL without next-time, and $\mathrm{PMCP}_{\mathcal{H}}(\{P\}, \cdot)$ restricted to $2$-indexed CTL without next-time, are undecidable.

For direction-unaware processes the same paper proves, for every set of topologies and all $k$ and $d$, a cutoff and hence decidability for $k$-indexed $\mathrm{CTL}^\ast_d\backslash\mathrm{X}$, the formulas of CTL* without next-time whose path quantifiers nest to depth at most $d$ (Theorem 7 and Corollary 8); without the depth bound this fails, as clause 3 shows (Theorem 14). For prenex universal CTL* without next-time it computes cutoffs on uni- and bi-directional rings, cliques and stars, so that problem is decidable there (Theorem 15).

## Depends on

- [Formulas of linear temporal logic](../../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [CTL formulas](../../../../../Logic/temporal-logic/computation-tree-logic/formula.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Clauses 1 and 2 reduce the non-halting problem of two-counter machines. The process that starts with the token becomes a controller simulating the finite control of the machine; the other processes are memory cells, each storing one bit per counter, so that a counter's value is the number of its bits set to $1$. Direction awareness lets the controller send commands around the ring and check, from the direction in which the token returns, whether an increment, a decrement or a zero test succeeded. A ring of size $n$ thus simulates the machine with counters bounded by about $n$; since a machine halts exactly when it halts with some bound on its counters, the machine does not halt exactly when the specification holds in every ring. A good expansion links a page for the simulation of bounded two-counter machines by direction-aware rings.

## Sources

- Benjamin Aminof, Swen Jacobs, Ayrat Khalimov and Sasha Rubin, *Parameterized Model Checking of Token-Passing Systems*, Verification, Model Checking, and Abstract Interpretation (VMCAI 2014), Lecture Notes in Computer Science 8318, Springer, 2014, pp. 262–281, https://doi.org/10.1007/978-3-642-54013-4_15; Section 2 (process templates, token-passing systems, indexed temporal logics and the PMCP), Theorem 14 and Theorem 17 of arXiv:1311.4425v3, the version read.
