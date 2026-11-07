# Microscopic weighting is not equivalent to finite concentration

It is not true that every
nonempty finite metric space $X$ has a microscopic weighting if and only if it has finite
concentration. Here, for real $t$, $Z_t$ is the $X \times X$ matrix with entries
$e^{-t\,d(x,y)}$ and $w_t = Z_t^{-1}\mathbf{1}$ is its weighting, where $\mathbf{1}$ is the
all-ones vector and the inverse of a singular matrix is taken to be $0$. The space $X$ has a
microscopic weighting if $w_t$ converges to some $w \colon X \to \mathbb{R}$ as $t \to 0^+$. It
has finite concentration if there are $g \colon X \to \mathbb{R}$ with $\sum_{x \in X} g(x) = 1$
and $c \in \mathbb{R}$ such that $\sum_{y \in X} d(x,y)\,g(y) = c$ for every $x \in X$.

Kenta Kitamura (assisted by ChatGPT) gave an explicit 10-point metric space with finite
concentration but no microscopic weighting.

## Sources

- Kenta Kitamura, microscopic-weighting-counterexample, Lean formalization of the 10-point counterexample, https://github.com/KitaKen1/microscopic-weighting-counterexample/blob/eff8979/lean/MicroscopicWeightingCounterexampleFC.lean#L886-L894. Moved from `OpenConjectures/Analysis/MicroscopicWeighting`.
