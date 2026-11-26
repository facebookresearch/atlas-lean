# Machine code under a memory-corrupting attacker

A *state* of the machine is a tuple $(M_c \mid M_d, R, pc)$ of a code memory $M_c$ and a data memory $M_d$, partial maps from addresses (words) to words with disjoint
domains, a register file $R$ mapping registers $r_0, \dots, r_{31}$ to words, and a program counter $pc$. Instructions, decoded from code memory, are
$\mathbf{label}\ w$ (a no-op carrying an immediate value), $\mathbf{add}\ r_d, r_s, r_t$, $\mathbf{addi}\ r_d, r_s, w$, $\mathbf{movi}\ r_d, w$, $\mathbf{bgt}\ r_s, r_t, w$,
$\mathbf{jd}\ w$ (direct jump), $\mathbf{jmp}\ r_s$ (computed jump), $\mathbf{ld}\ r_d, r_s(w)$, $\mathbf{st}\ r_d(w), r_s$ and $\mathbf{illegal}$. *Normal steps* $\to_n$ execute the
instruction at $pc$, which must lie in the domain of $M_c$ (data is not executable), and never write code memory (code is not writable). *Attack steps* $\to_a$
replace the data memory and the registers $r_3, \dots, r_{31}$ by arbitrary values, leaving code memory, the distinguished registers $r_0, r_1, r_2$ and the program
counter unchanged. The next-state relation is $\to\ =\ \to_n \cup \to_a$, so an attacker may corrupt data memory at any time.

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; author version of February 2007 at <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.1 (overview of the formal model) and Section 6.2 (states, instructions and the semantics $\to_n$, $\to_a$ and $\to$ of programs under attack).
