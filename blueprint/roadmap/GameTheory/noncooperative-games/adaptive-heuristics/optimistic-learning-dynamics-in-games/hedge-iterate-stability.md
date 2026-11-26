# Stability of Hedge and Optimistic Hedge iterates

Let $x^{t+1}(a) \propto x^t(a) \exp(-\eta\, m^t(a))$ on the simplex $\Delta_n$ with a vector $m^t$ whose coordinates lie in an interval of length at most $3$ (as for Optimistic Hedge with losses in $[0, 1]$, where $m^t = 2\ell^t - \ell^{t-1}$). Then for $0 < \eta \le 1/3$,

$$
\lVert x^{t+1} - x^t \rVert_1 \le e^{3\eta} - 1 \le 6\eta .
$$

## Proof sketch

Since normalization cancels any additive shift of $m^t$, assume its coordinates lie in $[0, 3]$; then each ratio $x^{t+1}(a)/x^t(a)$ lies in $[e^{-3\eta}, e^{3\eta}]$ after normalization, more precisely in $[Z^{-1} e^{-3\eta}, Z^{-1}]$ with $Z \in [e^{-3\eta}, 1]$. Hence $\lvert x^{t+1}(a) - x^t(a)\rvert \le (e^{3\eta} - 1) x^t(a)$, and summing over $a$ gives the first bound; convexity of the exponential on $[0, 1]$ gives $e^{3\eta} - 1 \le 6\eta$ when $3\eta \le 1$.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407.
- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924.
