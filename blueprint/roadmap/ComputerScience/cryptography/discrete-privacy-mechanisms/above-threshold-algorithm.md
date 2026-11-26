# AboveThreshold and the sparse vector technique

*AboveThreshold* answers a stream of queries $f_1, f_2, \dots$ of sensitivity $\Delta$ against a public threshold $T$: it draws a noisy threshold $\hat T = T + \rho$ once, then for each query draws fresh noise $\nu_i$ and outputs $\top$ and halts at the first $i$ with $f_i(x) + \nu_i \ge \hat T$, outputting $\bot$ for all earlier queries. The *sparse vector technique* restarts AboveThreshold after each $\top$, with the privacy budget divided among at most $c$ positive answers.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Laplace mechanism](../laplace-and-exponential-mechanisms/laplace-mechanism.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
