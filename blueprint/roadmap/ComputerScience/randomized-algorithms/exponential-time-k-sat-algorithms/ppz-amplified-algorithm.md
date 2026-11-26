# The PPZ algorithm on the randomized word RAM

Fix $k \ge 1$ and $c \in \mathbb{N}$. There is a randomized word-RAM program that on input $(k, c, \varphi)$ runs up to $R = 2^{\lceil (k-1)n/k \rceil} \cdot c$ independent PPZ rounds, stopping at the first satisfying assignment, such that every run halts within $R \cdot \mathrm{poly}(n, L)$ instructions using at most $2nR$ random draws; the output $1$ is always accompanied by a satisfying assignment in memory; and on satisfiable $\varphi$ the output is $0$ with probability at most $e^{-c}$.

## Proof sketch

Independent rounds give failure probability at most $(1 - 2^{-(1-1/k)n})^R \le e^{-c}$.

## Depends on

- [Forced values and the PPZ round](ppz-forced-values-and-round.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)

## Proof depends on

- [Satisfiability coding lemma: PPZ round success probability](ppz-round-success-probability.md)
- [Multiword counters on the word RAM](../../sorting-and-searching/word-ram-integer-algorithms/multiword-counter.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", 38th IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
