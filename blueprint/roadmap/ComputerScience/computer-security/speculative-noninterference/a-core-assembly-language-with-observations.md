# A core assembly language with leakage observations

$\mu\mathrm{ASM}$ has registers, among them a program counter $\mathit{pc}$, values in $\mathbb N \cup \{\bot\}$, and instructions $\mathbf{skip}$, assignment $x \leftarrow e$, conditional
assignment $x \xleftarrow{e'?} e$, $\mathbf{load}\ x, e$, $\mathbf{store}\ x, e$, $\mathbf{beqz}\ x, \ell$, $\mathbf{jmp}\ e$ and the speculation barrier $\mathbf{spbarr}$. A program is a finite
set of labelled instructions $n : i$ with distinct labels, one labelled $0$, and no branch $n : \mathbf{beqz}\ x, n + 1$; $p(n)$ is the instruction labelled $n$, or $\bot$. A
configuration $\sigma = \langle m, a\rangle$ is a memory $m : \mathbb N \to \mathbb N \cup \{\bot\}$ and a register assignment $a$ ($\bot$ only in $\mathit{pc}$, signalling termination).

The non-speculative evaluation relation $\sigma \xrightarrow{o} \sigma'$ executes $p(a(\mathit{pc}))$ and emits an observation exposing the program counter and memory addresses:
$\mathbf{load}\ x, e$ sets $x$ to $m(n)$ for $n = [\![e]\!](a)$ and emits $\mathbf{load}\ n$; $\mathbf{store}\ x, e$ writes $a(x)$ at $n$ and emits $\mathbf{store}\ n$; $\mathbf{beqz}\ x, \ell$
sets $\mathit{pc}$ to $\ell$ and emits $\mathit{pc}\ \ell$ if $a(x) = 0$, and otherwise sets $\mathit{pc}$ to $a(\mathit{pc}) + 1$ and emits $\mathit{pc}\ (a(\mathit{pc}) + 1)$; $\mathbf{jmp}\ e$ sets
$\mathit{pc}$ to $\ell = [\![e]\!](a)$ and emits $\mathit{pc}\ \ell$; $\mathbf{skip}$, assignments, conditional assignments and $\mathbf{spbarr}$ emit nothing. A *run* is a triple
$\langle \sigma, \tau, \sigma'\rangle$ with $\sigma \xrightarrow{\tau}{}^* \sigma'$ and $\sigma'$ final; $(\!|p|\!)$ is the set of runs and $(\!|p|\!)(\sigma)$ the trace of the run from $\sigma$. Only terminating programs
are considered.

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section III, Figure 4 (syntax), Figure 5 (selected rules) and Appendix A of the extended version, Figure 9 (all rules, including BEQZ-Unsat for a branch not taken).
