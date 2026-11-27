# Online-to-batch for mistake bounds: majority of prefix hypotheses is a PAC learner with $m + 1 \ge 2M/(\varepsilon\delta)$

Let $A$ be a deterministic (measurable) online learner with mistake bound $M$ on a Boolean class $C$, and let $D$ be a distribution on $X \times \{0,1\}$ realizable by $C$. Run $A$ on an i.i.d. sample $z_0, \ldots, z_{m-1}$ from $D$ and let $h_t$ be its hypothesis after the first $t$ examples ($0 \le t \le m$). Then:

1. $\sum_{t \le m}\mathbb{E}[\mathrm{err}_D(h_t)] \le M$ (on $m+1$ examples), so a uniformly random prefix hypothesis has expected error at most $M/(m+1)$;
2. the majority vote $h$ of $h_0, \ldots, h_m$ satisfies $(m+1)\,\mathbb{E}[\mathrm{err}_D(h)] \le 2M$;
3. hence $h$ is an $(\varepsilon, \delta)$-PAC learner for $C$ over realizable distributions whenever $2M \le \varepsilon\delta(m+1)$.

On countable domains, every Boolean class with finite optimal mistake bound (equivalently finite Littlestone dimension) is PAC learnable.

## Proof sketch

Because $h_t$ depends only on the first $t$ examples, its error equals the probability that $A$ errs on the fresh example $z_t$; summing over $t$ gives the expected number of mistakes, at most $M$. The majority vote errs only where at least half of the prefix hypotheses err, so its error is at most twice their average. Markov's inequality turns the expectation bound into the PAC guarantee.

## Depends on

- [The fundamental theorem of PAC learning](../../pac-learning/is-paclearnable-realizable-family-iff-ha.md)
- [Online classification protocol, mistakes and regret](../online-classification-protocol-mistakes-and-regret.md)

## Proof depends on

- [Littlestone's theorem for arbitrary label sets: optimal mistake bound equals the multiclass Littlestone dimension](multiclass-littlestone-theorem.md)

## Sources

- Nick Littlestone, "From On-Line to Batch Learning", Proceedings of the Second Annual Workshop on Computational Learning Theory, 1989.
- Nicolò Cesa-Bianchi, Alex Conconi and Claudio Gentile, "On the Generalization Ability of On-Line Learning Algorithms", IEEE Transactions on Information Theory, 2004.
