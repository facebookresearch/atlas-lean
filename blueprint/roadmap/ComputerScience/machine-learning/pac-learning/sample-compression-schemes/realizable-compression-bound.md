# Littlestone-Warmuth compression bound in the realizable setting

Let $C$ have a sample compression scheme of size $k$ whose reconstruction has measurable misclassification sets, and let $D$ be a distribution realizable by $C$. For $m$ i.i.d. examples and every $\varepsilon \in [0,1]$, the hypothesis $h_S$ reconstructed by the scheme satisfies

$$
D^m\big(\mathrm{err}_D(h_S) > \varepsilon\big) \le (m+1)^{k}(1-\varepsilon)^{m-k}.
$$

Hence the scheme's learner is an $(\varepsilon, \delta)$-PAC learner over the distributions realizable by $C$ whenever $(m+1)^k(1-\varepsilon)^{m-k} \le \delta$.

## Proof sketch

Fix one of the at most $(m+1)^k$ possible index lists $J$. The reconstructed hypothesis depends only on the examples indexed by $J$, so conditionally on them it must label at least $m - k$ independent fresh examples correctly, which a hypothesis of error above $\varepsilon$ does with probability at most $(1-\varepsilon)^{m-k}$. A union bound over index lists finishes.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)

## Sources

- N. Littlestone and M. K. Warmuth, "Relating Data Compression and Learnability", unpublished manuscript, 1986.
- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995.
