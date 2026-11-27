# Functional CLT for martingale difference arrays in D([0,1])

Let row $n$ of $\xi$ be a square-integrable martingale difference sequence for the filtration
$\mathcal F_n$, with predictable quadratic variation converging to the identity,
$\sum_{j < \lfloor n t \rfloor} E[\xi_{n,j}^2 \mid \mathcal F_{n,j}] \to t$ in probability for every
$t \in [0,1]$, and satisfying the unconditional Lindeberg condition
$\sum_{i<n} E[\xi_{n,i}^2 \mathbf 1\{|\xi_{n,i}| > \varepsilon\}] \to 0$ for every $\varepsilon > 0$. Assume also finite-dimensional convergence of
the step process to $Z$, an almost everywhere measurable map from a probability space into the space
$C([0,1])$ of continuous paths: for every finite set of times $I \subseteq [0,1]$,
$(\sum_{i < \lfloor n t \rfloor} \xi_{n,i})_{t \in I} \to (Z_t)_{t \in I}$ in distribution. Then the
step processes of the array converge in distribution to $Z$ in the Skorokhod $J_1$ topology on
$D([0,1])$. The proof uses Aldous's tightness criterion.

## Sources

- McLeish (1974), §3; Jacod–Shiryaev (2003), Theorems VI.4.5 and VI.4.13 and §VIII.3; Billingsley (1999), §18.
