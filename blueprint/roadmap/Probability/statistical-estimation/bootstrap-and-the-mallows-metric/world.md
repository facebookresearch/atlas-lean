# Bootstrap world of a data sequence

For data $x_0, x_1, \dots$ in a measurable space with a zero element and $n \in \mathbb{N}$, let $\hat P_n = \frac1n\sum_{i<n}\delta_{x_i}$ be the empirical distribution ($\hat P_0 = \delta_0$). The bootstrap world of the data is the probability measure on arrays $\omega = (\omega_{n,k})_{n,k \in \mathbb{N}}$ under which all entries are independent and each $\omega_{n,k}$ has law $\hat P_n$; the resample at size $n$ is $(\omega_{n,0}, \dots, \omega_{n,n-1})$. Because it depends only on the data, laws under the bootstrap world are the conditional laws of bootstrap statistics given the sample.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Annals of Statistics* 9 (1981), 1196–1217.
