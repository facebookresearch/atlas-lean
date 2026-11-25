# McLeish's martingale central limit theorem

On a probability space, let $X_{n,k}$ be a martingale difference array: for each row $n$ the partial sums $\sum_{j<k} X_{n,j}$ form a martingale with respect to a filtration $\mathcal{F}_n$. Consider the row sums $S_n = \sum_{k < r_n} X_{n,k}$. Assume

- (a) there is a finite $B$ with $E\big[\max_{k<r_n} X_{n,k}^2\big] \le B$ for all large $n$;
- (b) $\max_{k<r_n} |X_{n,k}| \to 0$ in probability;
- (c) $\sum_{k<r_n} X_{n,k}^2 \to v$ in probability, for a constant $v \ge 0$.

Then $S_n$ converges in distribution to $N(0, v)$. No independence and no conditional variance assumption is made.

## Sources

- D. L. McLeish, *Dependent central limit theorems and invariance principles*, Ann. Probab. 2 (1974) 620–628, Theorem (2.3), with the proof of Theorem (2.1). McLeish normalizes `v = 1`; here `v ≥ 0` is arbitrary (`v = 0` gives convergence to `0`).
