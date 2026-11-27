# Multiclass weak learnability relative to random guessing on lists

Let $H \subseteq Y^X$ and $\gamma > 0$. A learner is a **$\gamma$-weak multiclass learner** for $H$ in the sense of Brukhim, Daniely, Mansour and Moran if, for every $H$-realizable $D$, given a sample of size $m_0$ it outputs a hypothesis $w : X \to Y$ and a list size $k \ge 2$ such that

$$
\Pr_{(x,y) \sim D}[w(x) = y] \ge \frac{1}{k} + \gamma
$$

where the guarantee only needs to beat uniform guessing among $k$ candidate labels; equivalently, it is a weak learner relative to a $k$-list baseline that guesses uniformly from a list containing the correct label. For $Y = \{0,1\}$ and $k = 2$ this is the classical weak learning condition $\Pr[w(x) = y] \ge \tfrac{1}{2} + \gamma$.

## Depends on

- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- N. Brukhim, A. Daniely, Y. Mansour, S. Moran, "Multiclass Boosting: Simple and Intuitive Weak Learning Criteria", NeurIPS (2023), arXiv:2307.00642.
