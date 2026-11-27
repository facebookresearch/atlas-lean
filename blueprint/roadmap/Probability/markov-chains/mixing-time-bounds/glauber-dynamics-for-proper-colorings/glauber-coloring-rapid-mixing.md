# Rapid mixing of Glauber dynamics for colorings when q > 2 Delta

Let $G$ have $n \ge 1$ vertices and maximum degree $\Delta$, and let $q > \Delta$. The uniform distribution on proper $q$-colorings is nonempty, reversible and stationary for Glauber dynamics, and for nonempty $U$ the uniform distribution on $X_U(b)$ is reversible for the dynamics updating $U$. If $q > 2\Delta$ then for $0 < \varepsilon \le 1$

$$
t_{\mathrm{mix}}(\varepsilon) \le \Bigl\lceil \frac{q - \Delta}{q - 2\Delta}\, n\,(\log n - \log \varepsilon) \Bigr\rceil .
$$

With a frozen boundary and a nonempty update set $U \ne \varnothing$, started from any coloring agreeing with $b$ off $U$, the distance to the uniform law on $X_U(b)$ after $t$ steps is at most $(1 - c/|U|)^t |U|$ with $c = (q-2\Delta)/(q-\Delta)$; in particular, for $0 < \delta \le 1$, it is at most $\delta$ once $t \ge \frac{q-\Delta}{q-2\Delta}\, n (\log n - \log \delta)$ and $|U| \le n$.

## Proof sketch

Detailed balance holds because a single update between two colorings differing at one vertex has the same probability in both directions. For path coupling with Hamming distance, update two colorings differing at one vertex $v$ at the same uniform vertex $w$ with an optimal coupling of the two uniform color choices: they disagree afterwards with probability at most $1/(q-\Delta)$ if $w$ is a neighbor of $v$, never if $w = v$. This gives the contraction factor $1 - (1 - \Delta/(q-\Delta))/n$, and path coupling on the closed set of colorings agreeing with $b$ off $U$ gives the frozen form.

## Depends on

- [Glauber dynamics for proper colorings with a frozen boundary](glauber-dynamics-for-colorings.md)
- [Distance to stationarity and total-variation mixing time](../coupling-and-total-variation-mixing/distance-to-stationarity-and-mixing-time.md)
- [Reversible stochastic matrix](../../kolmogorov-s-criterion-for-reversibility/is-reversible.md)

## Proof depends on

- [Bubley-Dyer path coupling theorem](../coupling-and-total-variation-mixing/path-coupling-theorem.md)
- [Detailed balance implies stationarity](../../kolmogorov-s-criterion-for-reversibility/detailed-balance-is-stationary.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
