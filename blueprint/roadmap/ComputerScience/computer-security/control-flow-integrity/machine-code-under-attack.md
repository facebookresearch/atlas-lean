# Machine code under a memory-corrupting attacker

Words are natural numbers. A *state* of the machine is a tuple $(M_c \mid M_d, R, pc)$ of a memory split into a code memory $M_c$ with domain $\{0, \dots, n - 1\}$ for some
$n > 0$ (the program, whose first instruction is at $0$) and a data memory $M_d$ on the remaining addresses, a register file $R$ mapping registers $r_0, \dots, r_{31}$ to words, and a program counter $pc$. Instructions, decoded from code memory, are
$\mathbf{label}\ w$ (a no-op carrying an immediate value), $\mathbf{add}\ r_d, r_s, r_t$, $\mathbf{addi}\ r_d, r_s, w$, $\mathbf{movi}\ r_d, w$, $\mathbf{bgt}\ r_s, r_t, w$,
$\mathbf{jd}\ w$ (direct jump), $\mathbf{jmp}\ r_s$ (computed jump), $\mathbf{ld}\ r_d, r_s(w)$, $\mathbf{st}\ r_d(w), r_s$ and $\mathbf{illegal}$. *Normal steps* $\to_n$ execute the
instruction decoded from $M_c(pc)$ and are defined only when the **next** program counter is again in $\mathrm{dom}(M_c)$: $pc + 1$ for the straight-line instructions and a
branch not taken, the target for a taken $\mathbf{bgt}$, for $\mathbf{jd}\ w$ and for $\mathbf{jmp}\ r_s$ (whose target is $R(r_s)$); a store $\mathbf{st}\ r_d(w), r_s$ is defined only when
$R(r_d) + w \in \mathrm{dom}(M_d)$; and $\mathbf{illegal}$ has no step. So data is never executed and code is never written. *Attack steps* $\to_a$
replace the data memory and the registers $r_3, \dots, r_{31}$ by arbitrary values, leaving code memory, the distinguished registers $r_0, r_1, r_2$ and the program
counter unchanged. The next-state relation is $\to\ =\ \to_n \cup \to_a$, so an attacker may corrupt data memory at any time.

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; author version of February 2007 at <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Section 6.1 (overview of the formal model), Section 6.2.1 (machine model, the split $M = M_c \mid M_d$), Section 6.2.2 (instructions) and Section 6.2.3 with Figures 13–14 (the semantics $\to_n$, with its successor-program-counter and store conditions, $\to_a$ and $\to$); the relaxed semantics of Section 6.2.4 is a different model.
