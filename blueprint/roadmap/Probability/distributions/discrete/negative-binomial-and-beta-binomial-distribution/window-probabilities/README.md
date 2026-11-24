# Order statistics and window probabilities

Let $m, N, r, a, b \in \mathbb{N}$ with $1 \le r \le m + 1$ and $a < b$, and let $\mu$ be a probability measure on the space of score vectors, made of $m + 1$ real scores and $N$ synthetic scores, under which the scores are almost surely pairwise distinct; no exchangeability is needed. Let $S_{(r)}$ be the $r$-th smallest real score, $\tilde S_{(a)}$ the $a$-th smallest synthetic score for $1 \le a \le N$, with the convention $\tilde S_{(a)} = +\infty$ for every $a > N$, $J$ the number of synthetic scores strictly below $S_{(r)}$, and $F(t) = \mu(J + 1 \le t)$. Then

$$\mu\bigl( (a = 0 \ \text{or}\ \tilde S_{(a)} \le S_{(r)}) \ \text{and}\ S_{(r)} \le \tilde S_{(b)} \bigr) = F(b) - F(a),$$

where $a = 0$ plays the role of a $-\infty$ sentinel.

## Idea

The window event says that the real order statistic $S_{(r)}$ falls between two synthetic order statistics. When the scores are distinct, $\tilde S_{(a)} \le S_{(r)}$ means that at least $a$ synthetic scores lie below $S_{(r)}$, that is $J + 1 > a$, and $S_{(r)} \le \tilde S_{(b)}$ means that fewer than $b$ do, that is $J + 1 \le b$. So the event is $\{a < J + 1 \le b\}$ up to a null set, and its probability is $F(b) - F(a)$. This is an identity between events, which is why no exchangeability enters; ties would break it, which is why the scores must be almost surely distinct. Combined with the beta-binomial law of $J$ for exchangeable scores, it gives the exact probability that $S_{(r)}$ lands in a window between synthetic order statistics.

## Statements

- [Window probability for scores without ties](measure-real-window-of-ae-injective.md)
- [The $r$-th real order statistic](real-order-statistic.md): definition used in the main statement
- [The $a$-th synthetic order statistic](synthetic-order-statistic.md): definition used in the main statement
- [The $+\infty$ sentinel](synthetic-order-statistic-succ-eq-top.md): basic property of the synthetic order statistic
- [The real order statistic is a real score](exists-real-order-statistic-eq.md): lemma used for the window event
- [Window event for distinct scores](window-iff-of-injective.md): lemma used in the proof of the main statement
- [Window probability (i.i.d. atomless scores)](measure-real-window.md): i.i.d. atomless special case

## Background

- [Beta-binomial law of the sample rank](../sample-rank-law/README.md)
