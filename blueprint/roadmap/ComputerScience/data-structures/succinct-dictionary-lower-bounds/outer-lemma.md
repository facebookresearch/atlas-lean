# Outer lemma: each tree node forces many attributed probes or many probes

Let $U = n^{1+\alpha}$ for a constant $\alpha > 0$, let $\gamma = \alpha / (6(1+\alpha))$, let $\beta$ be the absolute constant of the Bloomier-filter encoding used in the inner game, and let $t > 0$. Consider a deterministic cell-probe scheme for the dynamic dictionary with at most $n$ keys of $[U]$, with cells of $w = \log_2 U$ bits and a memory of $\log_2 \binom{U}{n} + R$ bits, run on the insert–query–delete distribution, together with a meta-operation tree over its $n$ meta-operations. If a level-$\ell$ node $u$ satisfies

- $2^{64} \le \lambda_\ell \le \frac{\alpha}{12} \log_2 n$,
- $m_\ell \log_2 \lambda_\ell \ge 100 R$,
- $\frac{1}{2} \gamma\, m_\ell \log_2 U \ge R + 5 m_\ell + 2(\beta + 1) m_\ell t$, and
- $m_\ell \ge n^{1 - \gamma/2}$,

then $\mathbb{E}[\mathrm{cost}_u] \ge \frac{\gamma}{100} m_\ell$ or $\mathbb{E}[\mathrm{probe}_u] \ge \frac{1}{16} m_\ell t$.

## Proof sketch

Suppose both fail. In a one-way game Alice must tell Bob how the node's inserted key set $A$ is split among the $\lambda_\ell$ children's segments, which has entropy $\log_2 (m_\ell! / (m_{\ell-1}!)^{\lambda_\ell})$ given Bob's knowledge of $A$, the initial state, the deletions and the insertion orders. Alice first sends the final state, whose entropy given Bob's knowledge is at most about $R$ because its key set is determined by Bob's input. Then, segment by segment, Bob reconstructs the state before the segment and either receives the index of the true insertion set among the candidates passing a simulation test, or, when the segment probes too many cells, its index among all candidates. Few cells are probed in two different segments because $\mathrm{cost}_u$ is small, the inner lemma bounds the number of candidates passing the test, and Markov's inequality bounds how often a segment probes too many cells, so the message is shorter than the entropy, a contradiction.

## Depends on

- [Meta-operation tree and probe attribution](meta-operation-tree.md)
- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)
- [Information-theoretic space bound for dictionaries](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Inner communication game for succinct dictionaries](inner-communication-game.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
