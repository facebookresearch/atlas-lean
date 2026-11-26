# Speculative semantics with prediction oracles

A *prediction oracle* $O$ maps a [$\mu\mathrm{ASM}$ program](a-core-assembly-language-with-observations.md) $p$, a branching history $h$ (a sequence of triples of a branch label, a
transaction identifier and a predicted label) and the label $\ell$ of a branch $\mathbf{beqz}\ x, \ell''$ to a pair $\langle \ell', w\rangle$, a predicted target $\ell' \in \{\ell + 1, \ell''\}$ and a
transaction length $w$; $O$ has *speculative window at most* $w$ if every returned length is at most $w$.

The speculative semantics acts on extended configurations $\langle \mathit{ctr}, \sigma, s, h\rangle$, with $s$ a stack of speculative states $\langle \sigma_0, \mathit{id}, w, \ell\rangle$ (a snapshot, an
identifier, a remaining length and a prediction). At a branch it asks $O$ for $\langle \ell, w\rangle$, jumps to $\ell$, pushes a new transaction and emits $\mathbf{start}\ \mathit{id} \cdot \mathit{pc}\ \ell$; other
instructions step as in the non-speculative semantics and decrement all remaining lengths, while $\mathbf{spbarr}$ sets them to $0$. A transaction whose length reaches $0$
*commits* (emitting $\mathbf{commit}\ \mathit{id}$) if its prediction was right, and otherwise *rolls back* to its snapshot, discarding nested transactions and emitting
$\mathbf{rollback}\ \mathit{id} \cdot \mathit{pc}\ \ell'$ with $\ell'$ the correct target. $[\![p]\!]_O(\sigma)$ is the trace of the run from $\sigma$. The *non-speculative projection* $\tau{\upharpoonright_{\mathrm{nse}}}$
deletes every rolled-back segment $\mathbf{start}\ \mathit{id} \cdots \mathbf{rollback}\ \mathit{id}$ and every start, commit and rollback observation; then $(\!|p|\!) = [\![p]\!]_O{\upharpoonright_{\mathrm{nse}}}$
for every oracle $O$.

## Depends on

- [A core assembly language with leakage observations](a-core-assembly-language-with-observations.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section IV, the prediction oracles, speculative transactions, Figure 6 (rules SE-NoBranch, SE-Branch, SE-Commit, SE-Rollback), the projections and Proposition 1 (proved in Appendix F).
