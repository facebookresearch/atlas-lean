# Well-instrumented code for control-flow integrity

Let $G$ be a [control-flow graph](control-flow-graphs-of-machine-code.md) for a code memory $M_c$. The predicate $I(M_c, G)$ holds when

1. the last instruction of $M_c$ is $\mathbf{illegal}$, at the address $\mathit{HALT}$;
2. an address holds a $\mathbf{label}$ instruction exactly when it is a destination, and then the instruction is $\mathbf{label}\ w$ with $w$ its ID;
3. every computed jump is $\mathbf{jmp}\ r_0$, preceded by the check
   $\mathbf{addi}\ r_0, r_s, 0;\ \mathbf{ld}\ r_1, r_0(0);\ \mathbf{movi}\ r_2, \mathit{IMM};\ \mathbf{bgt}\ r_1, r_2, \mathit{HALT};\ \mathbf{bgt}\ r_2, r_1, \mathit{HALT}$,
   where $\mathit{IMM}$ encodes $\mathbf{label}$ of the jump's ID, so the jump proceeds only if its target holds the expected label;
4. no direct jump or branch targets a $\mathbf{jmp}$ instruction or one of the last four instructions of its check (it may target the initial $\mathbf{addi}$).

These are static conditions that a verifier can check after instrumentation.

## Depends on

- [Control-flow graphs of machine code](control-flow-graphs-of-machine-code.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; author version of February 2007 at <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.4.1, the verification conditions (1)–(4) and the predicate $I(M_c, G)$.
