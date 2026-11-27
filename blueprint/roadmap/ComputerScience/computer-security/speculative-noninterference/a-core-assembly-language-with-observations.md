# A core assembly language with leakage observations

$\mu\mathrm{ASM}$ has registers, among them a program counter $\mathit{pc}$, values in $\mathbb N \cup \{\bot\}$, and instructions $\mathbf{skip}$, assignment $x \leftarrow e$, conditional
assignment $x \xleftarrow{e'?} e$, $\mathbf{load}\ x, e$, $\mathbf{store}\ x, e$, $\mathbf{beqz}\ x, \ell$, $\mathbf{jmp}\ e$ and the speculation barrier $\mathbf{spbarr}$. A program is a finite
set of labelled instructions $n : i$ with distinct labels, one labelled $0$, and no branch $n : \mathbf{beqz}\ x, n + 1$; $p(n)$ is the instruction labelled $n$, or $\bot$. A
configuration $\sigma = \langle m, a\rangle$ is a memory $m : \mathbb N \to \mathbb N \cup \{\bot\}$ and a register assignment $a$ ($\bot$ only in $\mathit{pc}$, signalling termination).

The non-speculative evaluation relation $\sigma \xrightarrow{o} \sigma'$ executes $p(a(\mathit{pc}))$ and emits an observation exposing the program counter and memory addresses.
$\mathbf{skip}$ and $\mathbf{spbarr}$ only set $\mathit{pc}$ to $a(\mathit{pc}) + 1$. For a destination register $x \ne \mathit{pc}$ (there is no step otherwise): $x \leftarrow e$ sets $x$ to
$[\![e]\!](a)$; $x \xleftarrow{e'?} e$ sets $x$ to $[\![e]\!](a)$ if $[\![e']\!](a) = 0$ and leaves it unchanged otherwise; and $\mathbf{load}\ x, e$ sets $x$ to $m(n)$ for $n = [\![e]\!](a)$ and
emits $\mathbf{load}\ n$; each of these also sets $\mathit{pc}$ to $a(\mathit{pc}) + 1$, and only the load emits an observation. $\mathbf{store}\ x, e$ writes $a(x)$ at $n = [\![e]\!](a)$, sets
$\mathit{pc}$ to $a(\mathit{pc}) + 1$ and emits $\mathbf{store}\ n$. $\mathbf{beqz}\ x, \ell$ sets $\mathit{pc}$ to $\ell$ and emits $\mathit{pc}\ \ell$ if $a(x) = 0$, and otherwise sets $\mathit{pc}$ to
$a(\mathit{pc}) + 1$ and emits $\mathit{pc}\ (a(\mathit{pc}) + 1)$; $\mathbf{jmp}\ e$ sets $\mathit{pc}$ to $\ell = [\![e]\!](a)$ and emits $\mathit{pc}\ \ell$; and if $p(a(\mathit{pc})) = \bot$ the step sets
$\mathit{pc}$ to $\bot$ silently. A configuration is *initial* if $a(\mathit{pc}) = 0$ and *final* if $a(\mathit{pc}) = \bot$. A *run* is a triple $\langle \sigma, \tau, \sigma'\rangle$ with $\sigma$ initial,
$\sigma \xrightarrow{\tau}{}^* \sigma'$ and $\sigma'$ final; $(\!|p|\!)$ is the set of runs and, for an initial configuration $\sigma$, $(\!|p|\!)(\sigma)$ is the trace of the run from $\sigma$. Only terminating
programs are considered.

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section III, Figure 4 (syntax), Section III-B (initial and final configurations, runs and traces), Figure 5 (selected rules) and Appendix A of the extended version, Figure 9 (all rules: the destination condition $x \ne \mathit{pc}$ of Assign, ConditionalUpdate and Load, BEQZ-Unsat for a branch not taken, and Terminate).
