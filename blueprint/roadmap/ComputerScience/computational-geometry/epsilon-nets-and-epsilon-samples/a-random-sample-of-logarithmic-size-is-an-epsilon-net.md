# A random sample of logarithmic size is an ε-net

Let $(x, R)$ be a finite range space with $n = |x| \ge 1$ points and VC dimension at most $\delta$, where $\delta \ge 1$ is an integer, and let $\varepsilon, \varphi \in (0, 1)$. For the integer $m = \lceil (\delta \ln(n + 1) + \ln(1/\varphi))/\varepsilon \rceil$, the multiset $C$ of $m$ independent draws from the uniform distribution on $x$ is an $\varepsilon$-net for $x$ with probability at least $1 - \varphi$: a fixed range with at least $\varepsilon n$ points is missed with probability at most $(1 - \varepsilon)^m \le e^{-\varepsilon m}$, and the ranges meet $x$ in at most $\sum_{i \le \delta} \binom{n}{i} \le (n + 1)^\delta$ distinct sets.

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Proof depends on

- [Sauer-Shelah bound on traces](../../not-yet-classified/growth/card-trace-family-le-sum-vc-dim.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Lemma 7.3.10 and its proof, which this page follows with Sauer's lemma (Lemma 7.2.2) for an explicit sample size ("a naive proof of the ε-net theorem"; the lemma is stated for ε-samples but proved, as titled, for ε-nets)
