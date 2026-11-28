# Repeated coverability in broadcast networks is undecidable

The repeated coverability problem for broadcast protocols asks whether some infinite execution, for some number of processes, lets one process take a given broadcast transition infinitely often. No algorithm decides it. Restricted to Wait-Only protocols it becomes decidable, in EXPSPACE and PSPACE-hard.

**Problem (Guillou, Sangnier and Sznajder).** Repeated Coverability takes as input a [broadcast protocol](broadcast-protocols-and-their-networks.md) $\mathcal{P} = (Q, \Sigma, q_{in}, T)$ and a broadcast transition $t = (q, !!a, q') \in T$. The question is whether there exist an infinite execution $\rho = C_0 C_1 \cdots$ (starting in an initial configuration of some size $n \ge 1$) and a process $e \in \{1, \dots, n\}$ such that for every $i \in \mathbb{N}$ there is $j > i$ with $C_j \xrightarrow{e, t} C_{j+1}$, that is, process $e$ takes $t$ infinitely often.

**Theorem (Esparza, Finkel and Mayr; stated in this form by Guillou, Sangnier and Sznajder).** Repeated Coverability is undecidable.

It is a liveness question, while coverability of a state (a safety question) is decidable and Ackermann-complete for broadcast protocols. For Wait-Only protocols, where no state has both a broadcast and a reception, Guillou, Sangnier and Sznajder place Repeated Coverability in EXPSPACE and show it PSPACE-hard.

## Depends on

- [Broadcast protocols and their networks](broadcast-protocols-and-their-networks.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source that states the problem in this form does not reprove its undecidability; it cites Theorem 5.1 of Esparza, Finkel and Mayr, who show that liveness properties of broadcast protocols are undecidable. A good expansion reads that proof, links the undecidable problem it reduces from and checks that the cited theorem covers exactly the transition-based formulation above.

## Sources

- Lucie Guillou, Arnaud Sangnier and Nathalie Sznajder, "Wait-Only Broadcast Protocols Are Easier to Verify", 50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025), Leibniz International Proceedings in Informatics (LIPIcs) 345, pp. 53:1–53:17, 2025, <https://doi.org/10.4230/LIPIcs.MFCS.2025.53>. Read in arXiv:2506.22144v1, <https://arxiv.org/abs/2506.22144v1>; problem Repeated Coverability in Section 2.2, Theorem 2.4 (undecidability, attributed to Theorem 5.1 of the next source), coverability and liveness in Section 1, Wait-Only results in Section 5 and the abstract, numbering of arXiv:2506.22144v1.
- Javier Esparza, Alain Finkel and Richard Mayr, "On the Verification of Broadcast Protocols", Proceedings of the 14th Annual IEEE Symposium on Logic in Computer Science (LICS 1999), pp. 352–359, 1999, <https://doi.org/10.1109/LICS.1999.782630>; Theorem 5.1 as cited by the first source (not read).
