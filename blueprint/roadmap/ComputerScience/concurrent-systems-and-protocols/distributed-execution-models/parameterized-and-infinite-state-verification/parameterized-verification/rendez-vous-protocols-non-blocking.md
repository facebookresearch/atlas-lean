# Rendez-vous protocols with non-blocking semantics

A rendez-vous protocol is a finite-state process run by any number of identical copies that synchronize in pairs on messages. Under the non-blocking semantics a process may also send a message that no other process can receive, and then moves on alone.

**Protocols.** A rendez-vous protocol is $\mathcal{P} = (Q, \Sigma, q_{in}, q_f, T)$ with a finite set $Q$ of states, a finite alphabet $\Sigma$, an initial state $q_{in}$, a final state $q_f$ and a finite set $T \subseteq Q \times (\{\tau\} \cup \{!m, ?m : m \in \Sigma\}) \times Q$ of transitions: internal actions $\tau$, requests $!m$ (sending $m$) and answers $?m$ (receiving $m$). A configuration is a nonempty multiset $C$ over $Q$, where $C(q)$ is the number of processes in state $q$; it is initial if all its processes are in $q_{in}$.

**Non-blocking semantics.** For configurations $C, C'$ of the same size and $m \in \Sigma$:

- (internal) $C \to C'$ if $(q, \tau, q') \in T$, $C(q) > 0$ and $C' = C - \{q\} + \{q'\}$;
- (rendez-vous) $C \to C'$ if $(q_1, !m, q_1') \in T$ and $(q_2, ?m, q_2') \in T$, $C(q_1) > 0$, $C(q_2) > 0$, $C(q_1) + C(q_2) \ge 2$ and $C' = C - \{q_1, q_2\} + \{q_1', q_2'\}$;
- (non-blocking request) $C \to C'$ if $(q_1, !m, q_1') \in T$, $C(q_1) > 0$, no process of $C - \{q_1\}$ is in a state with an outgoing $?m$ transition, and $C' = C - \{q_1\} + \{q_1'\}$.

Here $\{q\}$ is the one-element multiset and $+$, $-$ are multiset sum and difference; $\to^*$ is the reflexive transitive closure of $\to$.

**Wait-only protocols.** $\mathcal{P}$ is wait-only if $Q$ splits into active states $Q_A \ni q_{in}$ and waiting states $Q_W$ such that no answer $?m$ leaves an active state and no request $!m$ and no internal action leaves a waiting state.

**Verification problems.** Given $\mathcal{P}$, the state coverability problem asks whether $C_0 \to^* C_f$ for some initial $C_0$ and some $C_f$ with $C_f(q_f) > 0$, and the synchronization problem asks whether $C_0 \to^* C_f$ for some initial $C_0$ and some $C_f$ all of whose processes are in $q_f$. The number of processes is not fixed: it is chosen by the initial configuration.

## Depends on

None.

## Proof depends on

None.

## Expansion

Under the classical blocking semantics a request waits until some process answers it, and both coverability and synchronization are solvable in polynomial time. With non-blocking requests, configuration coverability is complete for exponential space in general and solvable in polynomial time for wait-only protocols, while synchronization becomes undecidable.

## Sources

- Lucie Guillou, Arnaud Sangnier and Nathalie Sznajder, "Safety Analysis of Parameterised Networks with Non-Blocking Rendez-Vous", in *34th International Conference on Concurrency Theory (CONCUR 2023)*, Leibniz International Proceedings in Informatics 279, article 7, pp. 7:1–7:17, 2023, doi:[10.4230/LIPIcs.CONCUR.2023.7](https://doi.org/10.4230/LIPIcs.CONCUR.2023.7); read in arXiv:2307.04546v1 ([arXiv](https://arxiv.org/abs/2307.04546v1)): Definition 2.1 with the non-blocking semantics and Remark 2.3 in Section 2.1, the verification problems of Section 2.2, and the definition of wait-only protocols in Section 5, in the numbering of that version.
