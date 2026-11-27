# Always-mispredict speculative semantics

For a speculative window $w$, the *always-mispredict semantics* of a [$\mu\mathrm{ASM}$ program](a-core-assembly-language-with-observations.md) acts on triples
$\langle \mathit{ctr}, \sigma, s\rangle$ with a stack $s$ of speculative states as in the [speculative semantics](speculative-semantics-with-prediction-oracles.md), but uses primed helpers that act only
on the last (innermost) transaction: $\mathrm{enabled}'(s)$, $\mathrm{decr}'(s)$ and $\mathrm{zeroes}'(s)$ apply $\mathrm{enabled}$, $\mathrm{decr}$ and $\mathrm{zeroes}$ to the last speculative state of $s$
only, leaving the enclosing ones unchanged (and $\mathrm{enabled}'(\varepsilon)$ holds). While $\mathrm{enabled}'(s)$:

- a non-branch instruction steps as in the non-speculative semantics with the same observation, and $s$ becomes $\mathrm{decr}'(s)$, or $\mathrm{zeroes}'(s)$ for $\mathbf{spbarr}$, so a barrier
  expires only the innermost transaction;
- at $\mathbf{beqz}\ x, \ell'$ the branch is always mispredicted: the step goes to $\ell = \sigma(\mathit{pc}) + 1$ if $\sigma(x) = 0$ and to $\ell = \ell'$ otherwise, replaces $s$ by
  $\mathrm{decr}'(s) \cdot \langle \sigma, \mathit{id}, \min(w, \mathrm{wndw}(s) - 1), \ell\rangle$ with $\mathit{id}$ the value of $\mathit{ctr}$ before the step and $\mathrm{wndw}(s)$ the remaining length of the last
  transaction ($\infty$ if there is none, so an outermost transaction gets length $w$), increments $\mathit{ctr}$ and emits $\mathbf{start}\ \mathit{id} \cdot \mathit{pc}\ \ell$.

When the last transaction has expired, $s \cdot \langle \sigma_0, \mathit{id}, 0, \ell\rangle$, it always rolls back: with $\sigma_0 \to \sigma''$ one non-speculative step from its snapshot, the configuration
becomes $\sigma''$, the stack becomes $s$ and $\mathbf{rollback}\ \mathit{id} \cdot \mathit{pc}\ \sigma''(\mathit{pc})$ is emitted; only that transaction is popped, and the enclosing one continues
as if the nested branch had been predicted correctly. $\{\!|p|\!\}_w(\sigma)$ is the trace of the run from an initial configuration $\sigma$ to a final one with empty stack, when there is one.

## Depends on

- [Speculative semantics with prediction oracles](speculative-semantics-with-prediction-oracles.md)
- [A core assembly language with leakage observations](a-core-assembly-language-with-observations.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section V-C, the three modifications, Appendix C, Figure 10 (rules AM-NoBranch, AM-Branch, AM-Rollback, with $\mathrm{enabled}'$, $\mathrm{decr}'$ and $\mathrm{zeroes}'$ acting on the last transaction) and the definition of $\mathrm{wndw}$ in the appendix on the always-mispredict proofs.
