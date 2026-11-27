# An infinite Littlestone tree forbids rates faster than linear

If $H \subseteq \{0,1\}^X$ has an infinite Littlestone tree, then for every learner there is a realizable distribution $P$ such that

$$
\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge \frac{1}{32 n} \quad \text{for infinitely many } n ;
$$

in particular $H$ is not learnable faster than $R(n) = 1/n$.

## Proof sketch

Let $\mathbf{y} = (y_1, y_2, \dots)$ be i.i.d. fair bits and let $P_{\mathbf{y}}$ put mass $2^{-k-1}$ on the labelled point $(x_{\mathbf{y}_{\le k}}, y_{k+1})$ of the tree, for $k \ge 0$; every finite branch is realized, so each $P_{\mathbf{y}}$ is realizable. If the test point sits at depth $k$ and every training point sits at a smaller depth, the label $y_{k+1}$ is a fair coin independent of everything the learner sees, so it errs with probability $\tfrac12$; this event has probability $2^{-k-1}(1 - 2^{-k})^n$. Taking $k_n = \lceil 1 + \log_2 n \rceil$ makes the error at least $1/(32n)$ on average over $\mathbf{y}$ along $n \to \infty$, and Fatou's lemma gives a single realization of $\mathbf{y}$ with expected error above $1/(32n)$ infinitely often.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Theorem 4.6 and its proof.
