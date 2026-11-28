# Coverability in one-dimensional pushdown VASS with resets is undecidable

A one-dimensional pushdown vector addition system with resets has a finite control, a pushdown stack and one natural-number counter that can be incremented, decremented and reset to zero. Deciding whether a target state is reachable is undecidable, although it is decidable when the stack alphabet has one symbol besides the bottom marker.

**Setting (Schmitz and Zetzsche).** A *one-dimensional pushdown vector addition system with resets* (1-PRVASS) is $\mathcal{V} = (Q, \Gamma, A)$ with a finite set of states $Q$, a finite stack alphabet $\Gamma$ and a finite set of actions $A \subseteq Q \times I^\ast \times Q$, labeled by finite sequences of instructions from $I = \Gamma \cup \bar{\Gamma} \cup \{\mathsf{inc}, \mathsf{dec}, \mathsf{reset}\}$, where $\bar{\Gamma} = \{\bar{z} : z \in \Gamma\}$. Configurations are triples $(q, w, n) \in Q \times \Gamma^\ast \times \mathbb{N}$. The instruction $z$ pushes $z$ on the stack, $\bar{z}$ pops $z$ (only when $z$ is on top), $\mathsf{inc}$ adds $1$ to the counter, $\mathsf{dec}$ subtracts $1$ (only when the result is in $\mathbb{N}$), and $\mathsf{reset}$ sets the counter to $0$. An action $(q, u, q')$ moves from $(q, w, n)$ to $(q', w', n')$ if executing the instructions of $u$ in order leads from $(w, n)$ to $(w', n')$. The *coverability problem* asks, given a 1-PRVASS and states $s, t$, whether $(s, \varepsilon, 0)$ reaches $(t, w, n)$ for some $w \in \Gamma^\ast$ and $n \in \mathbb{N}$.

**Theorem (Schmitz and Zetzsche).** The coverability problem for one-dimensional pushdown vector addition systems with resets is undecidable.

When the stack alphabet is $\{a, \bot\}$ with a bottom-of-stack symbol $\bot$, the problem is decidable, by a result of Finkel and Sutre on two-dimensional VASS with one resettable and one zero-testable counter.

## Depends on

- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from reachability in two-counter Minsky machines, from $(s, 0, 0)$ to $(t, 0, 0)$. Counter values $(n_0, n_1)$ are encoded as the single number $2^{n_0} 3^{n_1}$, so the instructions become multiplication by $2$ or $3$, division by $2$ or $3$, and tests of non-divisibility by $2$ or $3$. The current number is kept in unary on top of the stack, above a record of the operations performed so far, and gadgets use the counter as scratch space to implement each operation only *weakly*: a forward step from $m$ may produce any $n$ up to the correct result (for example any $n \le f \cdot m$ for multiplication), and resets clear the counter between steps. After a forward phase that follows the machine and ends with the number $1$, a backward phase replays the recorded operations in reverse with weak inverse gadgets and must return to $1$, with downward errors in the opposite direction. Being reachable through both a downward-approximate forward run and a downward-approximate backward run forces the run to be exact, so the target state is coverable exactly when the Minsky machine reaches $(t, 0, 0)$.

## Sources

- Sylvain Schmitz and Georg Zetzsche, "Coverability Is Undecidable in One-Dimensional Pushdown Vector Addition Systems with Resets", Reachability Problems (RP 2019), Lecture Notes in Computer Science, pp. 193–201, 2019, <https://doi.org/10.1007/978-3-030-30806-3_15>; Theorem 1, Section 2 (1-PRVASS and the coverability problem) and Section 3 (the reduction from Minsky machines) of arXiv:1906.07069v1, read at <https://arxiv.org/abs/1906.07069v1>.
