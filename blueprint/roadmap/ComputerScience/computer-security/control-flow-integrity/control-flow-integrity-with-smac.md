# Control-flow integrity with software memory access control

**Theorem (Abadi, Budiu, Erlingsson and Ligatti).** In the permissive semantics, let $S_0 = (M_c \mid M_d, R, pc)$ with $pc = 0$ and $I_s(M_c, G)$ for a control-flow graph $G$ of $M_c$
([SMAC instrumentation](smac-instrumentation-conditions.md)), and let $S_0 \to S_1 \to \cdots \to S_n$. Then for every $i < n$, either $S_i \to_a S_{i+1}$ and $S_{i+1}.pc = S_i.pc$, or
$S_{i+1}.pc \in \mathrm{succ}(S_0.M_c, G, S_i.pc)$. Inline store checks replace the assumption that code is not writable, and inline jump checks the assumption that data is not
executable; the two mechanisms protect each other.

The proof shows by induction an invariant like that for [instrumented code](execution-invariant-for-instrumented-code.md), with an extra conjunct forbidding jumps into or
past the checks before a store.

## Depends on

- [Instrumentation for control-flow integrity with software memory access control](smac-instrumentation-conditions.md)

## Proof depends on

- [Stores checked by software memory access control stay in data memory](stores-checked-by-smac-stay-in-data-memory.md)
- [Execution invariant for instrumented code](execution-invariant-for-instrumented-code.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.5.2, Theorem 2, and Appendix A.2 (Propositions 5–6 and Lemma 7).
