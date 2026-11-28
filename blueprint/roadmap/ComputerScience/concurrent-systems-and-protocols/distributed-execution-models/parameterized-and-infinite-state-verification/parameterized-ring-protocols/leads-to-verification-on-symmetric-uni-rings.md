# Leads-to verification for symmetric unidirectional rings is undecidable

Whether a symmetric protocol on unidirectional rings of every size satisfies a leads-to property between two conjunctive state predicates is undecidable, even when each process is deterministic, self-disabling and has a constant-size state.

**Setting.** A *symmetric uni-ring protocol* runs $N > 1$ copies $P_0, \dots, P_{N-1}$ of one template process, each with a variable $x_i$ over a fixed finite domain $\{0, \dots, M-1\}$; $P_i$ reads $x_{i-1}$ and $x_i$ (indices modulo $N$) and writes $x_i$. The template is a finite set of actions $(a, b, c)$, meaning: if $x_{i-1} = a$ and $x_i = b$ then $x_i$ may be set to $c$. Processes act one at a time (interleaving semantics) and no fairness is assumed. A process is *deterministic* if no two actions $(a, b, c)$, $(a, b, d)$ with $c \ne d$ coexist, and *self-disabling* if no actions $(a, b, c)$ and $(a, c, d)$ coexist. A *conjunctive state predicate* has the form $\forall i \in \mathbb{Z}_N:\ q(x_{i-1}, x_i)$ for a binary relation $q$ on the domain. A computation is a maximal sequence of global states $s_0, s_1, \dots$ in which each step is one action of one process: it is infinite, or it ends in a deadlock, a state in which no action is enabled (the proof of Theorem 3.2 of the source uses that $R \leadsto Q$ requires freedom from deadlocks and livelocks outside $Q$). It satisfies $R \leadsto Q$ if $s_0 \in R$ implies $s_j \in Q$ for some $j \ge 0$; the protocol satisfies $R \leadsto Q$ if every computation does, for every ring size $N$.

**Theorem (Ebnenasir).** The following problem is undecidable: given the action set of a template process of a symmetric uni-ring protocol whose processes are deterministic, self-disabling and constant-space, and conjunctive state predicates $R$ and $Q$, does the protocol satisfy $R \leadsto Q$ for all ring sizes?

The domain size $M$ and the actions are part of the input; the ring size is universally quantified. In contrast, the paper shows that synthesis, deciding whether some such protocol satisfies $R \leadsto Q$ for all ring sizes, is decidable.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Satisfying $R \leadsto Q$ without fairness requires that computations starting in $R$ neither deadlock nor livelock outside $Q$. The proof derives undecidability from the undecidability of livelock-freedom for symmetric uni-ring protocols of self-disabling deterministic processes, a result of Klinkhamer and Ebnenasir that the paper recalls (also for deterministic livelocks, in which exactly one process is enabled in each state). A good expansion links a page for that result.

## Sources

- Ali Ebnenasir, "Verification and Synthesis of Symmetric Uni-Rings for Leads-To Properties", Formal Methods in Computer Aided Design (FMCAD 2019), pp. 78–86, IEEE, 2019, <https://doi.org/10.23919/FMCAD.2019.8894272>; Problem 3.1, Theorem 3.2 and its proof, and the model, determinism, self-disabling and leads-to definitions of Section 2 of arXiv:1905.09726v1 (the copy read), <https://arxiv.org/abs/1905.09726v1>.
