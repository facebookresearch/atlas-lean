# Speculative semantics with prediction oracles

A *prediction oracle* $O$ maps a [$\mu\mathrm{ASM}$ program](a-core-assembly-language-with-observations.md) $p$, a branching history $h$ (a sequence of triples of a branch label, a
transaction identifier and a predicted label) and the label $\ell$ of a branch $\mathbf{beqz}\ x, \ell''$ to a pair $\langle \ell', w\rangle$, a predicted target $\ell' \in \{\ell + 1, \ell''\}$ and a
transaction length $w$; $O$ has *speculative window at most* $w$ if every returned length is at most $w$.

The speculative semantics acts on extended configurations $\langle \mathit{ctr}, \sigma, s, h\rangle$: a transaction counter, a configuration, a stack $s$ of speculative states
$\langle \sigma_0, \mathit{id}, w, \ell\rangle$ (a snapshot, an identifier, a remaining length and a prediction) and a branching history. Write $\mathrm{decr}(s)$ and $\mathrm{zeroes}(s)$ for $s$ with
every remaining length decreased by $1$, respectively set to $0$, and $\mathrm{enabled}(s)$ when no remaining length in $s$ is $0$. While $\mathrm{enabled}(s)$:

- a non-branch instruction steps as in the non-speculative semantics with the same observation, and $s$ becomes $\mathrm{decr}(s)$, or $\mathrm{zeroes}(s)$ for $\mathbf{spbarr}$;
- at $\mathbf{beqz}\ x, \ell''$ with $\sigma = \langle m, a\rangle$, the oracle gives $O(p, h, a(\mathit{pc})) = \langle \ell, w\rangle$; the step sets $\mathit{pc}$ to $\ell$, replaces $s$ by
  $\mathrm{decr}(s) \cdot \langle \sigma, \mathit{id}, w, \ell\rangle$ with $\mathit{id}$ the value of $\mathit{ctr}$ before the step (so a nested branch consumes a step of every
  enclosing transaction), increments $\mathit{ctr}$, appends $\langle a(\mathit{pc}), \mathit{id}, \ell\rangle$ to $h$ and emits $\mathbf{start}\ \mathit{id} \cdot \mathit{pc}\ \ell$.

When the stack has the form $s \cdot \langle \sigma_0, \mathit{id}, 0, \ell\rangle \cdot s'$ with $\mathrm{enabled}(s')$, the expired transaction is resolved by one step of the non-speculative
semantics from its snapshot, $\sigma_0 \to \langle m, a\rangle$, with $\langle \sigma_0(\mathit{pc}), \mathit{id}, a(\mathit{pc})\rangle$ appended to $h$. If $\ell = a(\mathit{pc})$ it *commits*: the stack becomes
$s \cdot s'$, the configuration is unchanged, and $\mathbf{commit}\ \mathit{id}$ is emitted. Otherwise it *rolls back*: the configuration becomes $\langle m, a\rangle$, resuming at the corrected
$\mathit{pc}$, the stack becomes $s$ (nested transactions are discarded), and $\mathbf{rollback}\ \mathit{id} \cdot \mathit{pc}\ a(\mathit{pc})$ is emitted. A run starts from
$\langle 0, \sigma, \varepsilon, \varepsilon\rangle$ with $\sigma$ initial and ends at $\langle \mathit{ctr}, \sigma', \varepsilon, h\rangle$ with $\sigma'$ final; $[\![p]\!]_O(\sigma)$ is its trace. The *non-speculative
projection* $\tau{\upharpoonright_{\mathrm{nse}}}$ deletes every rolled-back segment $\mathbf{start}\ \mathit{id} \cdots \mathbf{rollback}\ \mathit{id}$ and every start, commit and rollback observation. For every oracle $O$, the projection of
a completed speculative run is the non-speculative run from the same initial configuration: $[\![p]\!]_O(\sigma){\upharpoonright_{\mathrm{nse}}} = (\!|p|\!)(\sigma)$ whenever the left side is defined. The
converse needs speculative execution to keep stepping until every transaction resolves, which the rules do not guarantee: a mispredicted path can reach a
configuration with a positive remaining length at which no rule applies. The source's Proposition 1 states the equality
$(\!|p|\!) = [\![p]\!]_O{\upharpoonright_{\mathrm{nse}}}$ of the sets of runs; its completeness direction assumes this progress.

## Depends on

- [A core assembly language with leakage observations](a-core-assembly-language-with-observations.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section IV, the prediction oracles, speculative transactions, Figure 6 (rules SE-NoBranch, SE-Branch, SE-Commit, SE-Rollback), the projections and Proposition 1, proved in Appendix F over runs in $\mathrm{InitConf} \times \mathrm{ExtObs}^* \times \mathrm{FinalConf}$.
