# No class with three concepts is learnable faster than exponentially

Let $H \subseteq \{0,1\}^X$ contain at least three concepts. Then for every learner there is a realizable distribution $P$ such that

$$
\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge 2^{-n-2} \quad \text{for infinitely many } n ;
$$

in particular $H$ is not learnable faster than $R(n) = e^{-n}$. The hypothesis is needed: if $|H| = 1$ or $H = \{h, 1 - h\}$, error $0$ is achievable for every $n$ (the second case from a single example).

## Proof sketch

Since $|H| \ge 3$, there are $h_1, h_2 \in H$ and points $x, x'$ with $h_1(x) = h_2(x) = y$ and $h_1(x') \ne h_2(x')$. For $i \in \{0,1\}$ let $P_i$ put mass $\tfrac12$ on $(x, y)$ and mass $\tfrac12$ on $(x', i)$; both are realizable. Draw $I$ uniformly from $\{0,1\}$ and train on $P_I$: with probability $2^{-n-1}$ all $n$ training points equal $x$ and the test point is $x'$, and then the learner errs with conditional probability $\tfrac12$. So for each $n$ some $P_{i_n}$ has expected error at least $2^{-n-2}$, and by the pigeonhole principle one index $i$ occurs for infinitely many $n$.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Lemma 4.2 (after Schuurmans, 1997) and footnote 2.
