# Guessing probability, min-entropy and collision probability

Let $s$ be a random variable on a finite set $S$ with mass function $p$. Its *guessing probability* is $\gamma(s) = \max_x p(x)$, its *min-entropy* is $H_\infty(s) = -\log_2 \gamma(s)$, and its *collision probability* is $\mathrm{CP}(s) = \sum_x p(x)^2$, the probability that two independent copies coincide. A source has min-entropy at least $k$ exactly when every outcome has probability at most $2^{-k}$.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>
- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, <https://people.seas.harvard.edu/~salil/pseudorandomness/>
