# Dominating supermartingales bound the Snell envelope

Let $\mu$ be a finite measure, $(\mathcal{G}_k)$ a filtration, and $(G_k)$ a reward sequence with
every $G_k$ integrable, and let $S$ be the [Snell envelope](snell-envelope.md) with horizon $N$.
Let $(Y_k)$ be integrable with $\mathbb{E}[Y_{k+1} \mid \mathcal{G}_k] \le Y_k$ almost everywhere
for $k < N$ and $G_k \le Y_k$ almost everywhere for $k \le N$. Then $S_n \le Y_n$ almost
everywhere for every $n \le N$. Adaptedness of $Y$ is not assumed.

When the rewards are moreover adapted, $S$ is itself a [supermartingale](supermartingale-snell-envelope.md)
dominating the reward up to the horizon ([domination](le-snell-envelope.md)), so this makes $S$ the
smallest such supermartingale (Peskir and Shiryaev, Theorem 1.2).

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in
  Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, Theorem 1.2 (finite horizon), part
  (1.1.13). The book states it for supermartingales, which are adapted; the proof by backward
  induction does not use adaptedness.
