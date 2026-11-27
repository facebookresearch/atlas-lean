# Instrumentation for control-flow integrity with software memory access control

The SMAC variant of the [machine under attack](machine-code-under-attack.md) has a bounded memory: for some $n > 0$ and $B \ge n$, the memory has domain $\{0, \dots, B\}$,
with code memory $M_c$ on $\{0, \dots, n - 1\}$ and nonempty data memory $M_d$ on $\{n, \dots, B\}$, so that $\min(M_c) = 0$, $\max(M_c) = n - 1$, $\min(M_d) = n$ and $\max(M_d) = B$
are known when the code is instrumented. In its *permissive semantics*, normal steps execute the instruction at any address of $\{0, \dots, B\}$ and may store to any address of
$\{0, \dots, B\}$, dropping the assumptions that code is not writable and data not executable, and are defined only when the next program counter and the store or load address
lie in $\{0, \dots, B\}$; attack steps replace the data memory and the registers $r_3, \dots, r_{31}$ as before and still cannot change code memory, the distinguished registers or the
program counter. The predicate $I_s(M_c, G)$ holds of $M_c$ and a [control-flow graph](control-flow-graphs-of-machine-code.md) $G$ when

1. the last instruction of $M_c$ is $\mathtt{illegal}$, at address $\mathit{HALT}$;
2. the destinations of $G$ are exactly the addresses holding $\mathtt{label}$ instructions, each labelled with its destination's identifier;
3. every store is $\mathtt{st}\ r_0(0), r_s$ preceded by $\mathtt{addi}\ r_0, r_d, w$; $\mathtt{movi}\ r_1, \max(M_d)$; $\mathtt{movi}\ r_2, \min(M_d)$; $\mathtt{bgt}\ r_0, r_1, \mathit{HALT}$; $\mathtt{bgt}\ r_2, r_0, \mathit{HALT}$,
   which confines it to data memory;
4. every computed jump, at an address $w_0$, is $\mathtt{jmp}\ r_0$ preceded by exactly the nine instructions $\mathtt{addi}\ r_0, r_s, 0$; $\mathtt{movi}\ r_1, \max(M_c)$; $\mathtt{movi}\ r_2, \min(M_c)$;
   $\mathtt{bgt}\ r_0, r_1, \mathit{HALT}$; $\mathtt{bgt}\ r_2, r_0, \mathit{HALT}$; $\mathtt{ld}\ r_1, r_0(0)$; $\mathtt{movi}\ r_2, \mathit{IMM}$; $\mathtt{bgt}\ r_1, r_2, \mathit{HALT}$; $\mathtt{bgt}\ r_2, r_1, \mathit{HALT}$, for some
   register $r_s$, where $\mathit{IMM}$ is the word that decodes to the $\mathtt{label}$ instruction carried by the destinations of $w_0$; this confines $r_0$ to code memory and halts
   unless the word there is that label;
5. every target $w$ of a $\mathtt{bgt}$ or $\mathtt{jd}$ instruction is in code memory and holds neither a store or computed jump nor any instruction of the sequences in 3 and 4
   preceding them, except possibly their first instruction ($\mathtt{addi}\ r_0, r_d, w$, respectively $\mathtt{addi}\ r_0, r_s, 0$).

## Depends on

- [Machine code under attack](machine-code-under-attack.md)
- [Control-flow graphs of machine code](control-flow-graphs-of-machine-code.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.2.4 (the permissive semantics, Figure 15) and Section 6.5.1 (conditions (1)–(5), the predicate $I_s$, and the minimum and maximum code and data addresses known at instrumentation time). The source's memory is total on all words; the bounded domain $\{0, \dots, B\}$ above makes those maxima exist.
