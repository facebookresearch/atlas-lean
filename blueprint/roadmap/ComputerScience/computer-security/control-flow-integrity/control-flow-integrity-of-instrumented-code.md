# Instrumented code follows its control-flow graph despite attacks

**Theorem (Abadi, Budiu, Erlingsson and Ligatti).** Let $S_0 = (M_c \mid M_d, R, pc)$ be a state of the [machine under attack](machine-code-under-attack.md) with $pc = 0$ and
$I(M_c, G)$ for a [control-flow graph](control-flow-graphs-of-machine-code.md) $G$ of $M_c$ ([well-instrumented code](cfi-instrumentation-conditions.md)), and let
$S_0 \to S_1 \to \cdots \to S_n$. Then for every $i < n$, either $S_i \to_a S_{i+1}$ and $S_{i+1}.pc = S_i.pc$, or $S_{i+1}.pc \in \mathrm{succ}(S_0.M_c, G, S_i.pc)$.

So, whatever the attacker writes into data memory, the program counter always follows the CFG; in particular code unreachable in the CFG never runs. The proof
is an induction on executions with an invariant on the distinguished registers inside the instrumentation sequences, and relies on data memory being
non-executable.

## Depends on

- [Well-instrumented code for control-flow integrity](cfi-instrumentation-conditions.md)
- [Machine code under a memory-corrupting attacker](machine-code-under-attack.md)
- [Control-flow graphs of machine code](control-flow-graphs-of-machine-code.md)

## Proof depends on

- [Execution invariant for instrumented code](execution-invariant-for-instrumented-code.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.4.2, Theorem 1, and Appendix A.1 (its proof).
