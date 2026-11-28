# Monte Carlo Steiner minimum cut with polylogarithmically many max-flow calls

There is a randomized algorithm that, given an undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and integer weights in $\{1, \dots, W\}$ with $W \le n^{O(1)}$, and terminals $R \subseteq V$ with $|R| \ge 2$, uses $O(\log^3 n)$ max-flow calls and $O(m \log^2 n)$ additional time and outputs an $R$-Steiner cut that is a Steiner minimum cut with probability at least $1 - n^{-c}$, for any fixed constant $c > 0$ (Monte Carlo; the output is always a valid Steiner cut). In particular the global minimum cut ($R = V$) and the Steiner minimum cut can be computed in $m^{1+o(1)}$ randomized time using the almost-linear maximum-flow algorithm.

## Proof sketch

For each of the $\lfloor \log_2 |R| \rfloor$ sample sizes $2^i$, $i = 1, \dots, \lfloor \log_2 |R| \rfloor$, repeat $O(\log n)$ times: let $R'$ be a uniformly random subset of exactly $2^i$ terminals, run the isolating cut lemma on $R'$ and keep the lightest isolating cut found. Every candidate is a Steiner cut of $R$, since $|R'| = 2^i \ge 2$. For $k = |S^{*} \cap R| \le |R|/2$ as in the subsampling lemma, the size $2^i$ with $i = \lfloor \log_2(|R|/k) \rfloor$ is among those tried, and by that lemma each of its trials yields $\lambda_R(G)$ with probability $\Omega(1)$, so $O(\log n)$ trials succeed with probability $1 - n^{-c}$. Each isolating cut invocation costs $O(\log n)$ max-flow calls, giving $O(\log^3 n)$ calls in total.

## Depends on

- [Steiner minimum cuts of a terminal set](steiner-minimum-cut.md)
- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)

## Proof depends on

- [Terminal subsampling isolates one side of a Steiner minimum cut](terminal-subsampling-isolates-steiner-cut.md)
- [Isolating cut lemma with logarithmically many max-flow calls](isolating-cut-lemma.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
