# Boundedness of two identical communicating finite-state machines is undecidable

For a system of two identical finite-state machines that communicate through two perfect unbounded one-way FIFO channels, it is undecidable whether the reachability set or the reachability tree is finite, even when the machines are built from cycles through their initial states, start in the same state and the channels start empty.

**Systems of two machines.** A *communicating finite-state machine* (CFSM) is a finite automaton $A = (Q, q_0, \Sigma, \delta)$ with transitions $\delta \subseteq Q \times (\{+, -\} \times \Sigma) \times Q$, where $-a$ sends $a$ and $+a$ receives $a$. $A$ is *initial* if from every accessible state there is a path of transitions back to $q_0$. A system $S = (A_1, A_2)$ has global states $(q_1, q_2, w_{12}, w_{21})$, where $w_{ij} \in \Sigma^*$ is the content of the channel from $A_i$ to $A_j$; a send $-a$ by $A_i$ appends $a$ to $w_{ij}$, and a receive $+a$ by $A_i$ removes $a$ from the head of $w_{ji}$. For a global state $s_0$, the *reachability set* $RS(S, s_0)$ is the set of global states reachable from $s_0$, and the *reachability tree* $RT(S, s_0)$ is the tree rooted at $s_0$ in which a node labeled $s$ has a child for each successor of $s$. The *boundedness problem* asks whether $RS(S, s_0)$ is finite, and the *finite reachability tree problem* whether $RT(S, s_0)$ is finite.

**Theorem (Finkel and McKenzie).**

1. The boundedness problem and the finite reachability tree problem are undecidable for systems of two identical initial CFSMs, with the initial global state part of the input (Theorem 3.9).
2. Both problems remain undecidable when the two CFSMs are initial and identical, have identical starting states, and both channels are initially empty (Theorem 4.2).

## Depends on

None.

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

From a deterministic Turing machine $M$ that halts exactly on the inputs it accepts, and that otherwise moves its head arbitrarily far right, and an input $w$, the proof builds one CFSM $S(M)$ that is used twice and an initial global state whose channels hold the encoded initial configuration. Each copy is made of cycles through its initial state: it reads the current configuration of $M$ from its input channel, copying symbols to its output channel until it reaches the vicinity of the head, where it emits the vicinity after one step of $M$; the two copies advance the simulation in alternation, and blank-insertion cycles extend the tape. $M$ accepts $w$ iff the reachability tree is finite iff the reachability set is finite. For clause 2, extra initialization cycles act as a one-time mutual exclusion that lets either copy write the initial configuration first, without creating new infinite branches. Systems of two arbitrary CFSMs were already known to be Turing powerful (Brand and Zafiropulo).

## Sources

- Alain Finkel and Pierre McKenzie, "Verifying identical communicating processes is undecidable", *Theoretical Computer Science* 174(1–2):217–230, 1997, doi:10.1016/S0304-3975(96)00026-6; read in the authors' open-access preprint at <https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/FMK-TCS97.pdf>: Section 2 (CFSMs, systems, the reachability set and tree, and the two problems) and Theorems 3.9 and 4.2 of that copy.
