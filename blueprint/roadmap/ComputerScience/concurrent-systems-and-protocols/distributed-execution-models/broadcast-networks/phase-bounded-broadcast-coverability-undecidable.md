# Coverability of phase-bounded broadcast networks is undecidable

In networks of identical finite-state processes that broadcast messages to their neighbors in an arbitrary communication topology, whether some process can reach an error state is undecidable even when each process may switch between broadcasting and receiving phases at most $6$ times, or at most $4$ times when the topology is a line.

**Setting (Guillou, Sangnier and Sznajder).** A *broadcast protocol* is $\mathcal{P} = (Q, \Sigma, q_{\mathrm{in}}, \Delta)$ with finite states $Q$, finite message alphabet $\Sigma$, initial state $q_{\mathrm{in}}$ and transitions $\Delta \subseteq Q \times ({!!}\Sigma \cup {?}\Sigma \cup \{\tau\}) \times Q$ (broadcast, reception, internal action). A *topology* is a finite undirected graph without self-loops; line and tree topologies are the usual special cases. A configuration labels each vertex with a state; initial configurations label every vertex $q_{\mathrm{in}}$. In one step a vertex takes an internal transition, or broadcasts $m$ and moves, while every neighbor that can receive $m$ in its current state takes a reception transition on $m$ and every other neighbor stays put. For $k \in \mathbb{N}$, $\mathcal{P}$ is *$k$-phase-bounded* if $Q$ can be partitioned into $Q_0, Q^b_1, Q^r_1, \dots, Q^b_k, Q^r_k$ with $q_{\mathrm{in}} \in Q_0$ such that internal moves stay within a part, broadcasts stay in $Q^b_i$ or move from $Q^r_i$ (or $Q_0$) to $Q^b_{i+1}$, and receptions stay in $Q^r_i$ or move from $Q^b_i$ (or $Q_0$) to $Q^r_{i+1}$, or from $Q^b_k$ to $Q^r_k$; so each process alternates at most $k$ times between broadcasting and receiving, and may still receive in its last broadcasting phase. The *coverability problem* $\mathrm{Cover}[\mathcal{S}]$ for a family $\mathcal{S}$ of topologies asks, given $\mathcal{P}$ and a state $q_f$, whether for some topology in $\mathcal{S}$ some execution from the initial configuration reaches a configuration in which some vertex is in $q_f$.

**Theorem (Guillou, Sangnier and Sznajder).**

1. For every fixed $k \ge 6$, coverability restricted to $k$-phase-bounded protocols is undecidable, both over all topologies and over tree topologies.
2. For every fixed $k \ge 4$, coverability over line topologies restricted to $k$-phase-bounded protocols is undecidable.

For unrestricted protocols all three problems were already known to be undecidable (Delzanno, Sangnier and Zavattaro). The same paper shows that for $1$-phase-bounded protocols coverability over all topologies is EXPSPACE-complete, for $2$-phase-bounded protocols it is decidable, and over lines it is in polynomial time for $k \le 2$.

## Depends on
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem of two-counter Minsky machines. The protocol first forces the selection of a line of active vertices inside the topology (simpler when the topology is already a line, which saves two phases). The head of the line follows the control locations of the machine; the inner vertices store the counters, each in a state $\mathsf{zero}$, $1_{\mathsf{x}_1}$ or $1_{\mathsf{x}_2}$, so a counter's value is the number of vertices in its unit state; the tail checks the simulation. Operations travel along the line by each vertex repeating what its predecessor broadcast: an increment or decrement makes exactly one vertex change state, and a zero test of $\mathsf{x}$ cannot pass a vertex in $1_{\mathsf{x}}$. When the head reaches the halting location, a message propagates to the tail, which then enters $q_f$; the constructed protocol is $6$-phase-bounded ($4$ for lines).

## Sources

- Lucie Guillou, Arnaud Sangnier and Nathalie Sznajder, "Phase-Bounded Broadcast Networks over Topologies of Communication", 35th International Conference on Concurrency Theory (CONCUR 2024), LIPIcs 311, Article 26, 2024, <https://doi.org/10.4230/LIPIcs.CONCUR.2024.26>; read in arXiv:2406.15202v2, <https://arxiv.org/abs/2406.15202v2>: the definitions of Sections 2 and 3, Theorems 4.2 ($k \ge 6$, all topologies and trees) and 4.3 ($k \ge 4$, lines) in Section 4 ("Undecidability Results"), Theorem 5.6, and the summary table, in the numbering of that version.
