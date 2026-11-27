# Parallel Moser-Tardos algorithm: logarithmically many rounds

In the *parallel Moser-Tardos algorithm*, each round selects a maximal set of pairwise non-adjacent events among those that hold in the current assignment and resamples all of them; it stops when no event holds. Under the plain hypothesis $\Pr[A_i] \le x_i\prod_{j\in\Gamma(i)}(1-x_j)$, every such rule almost surely reaches an assignment avoiding all events, with at most $\sum_i x_i/(1-x_i)$ expected resamplings in total. If moreover $\Pr[A_i] \le (1-\varepsilon)\,x_i\prod_{j\in\Gamma(i)}(1-x_j)$ for some $\varepsilon \in (0,1]$, then the number $R$ of non-empty rounds satisfies

$$
\Pr[R \ge k+1] \le \min\Bigl(1,\ (1-\varepsilon)^{k+1}\sum_i \frac{x_i}{1-x_i}\Bigr), \qquad \mathbb{E}[R] \le \frac{\max\bigl(0, \log\sum_i \frac{x_i}{1-x_i}\bigr) + 1}{\varepsilon}.
$$

## Proof sketch

Every prefix of the parallel run is a valid sequential log, so the sequential bound applies to the total work. An event resampled in round $k$ has a witness tree of depth $k$ with at least $k+1$ vertices; with slack, each vertex contributes an extra factor $1-\varepsilon$, so the witness-tree sum gives the tail bound, and summing tails gives the expected number of rounds.

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)

## Proof depends on

- [Moser-Tardos witness tree lemma](moser-tardos-witness-tree-lemma.md)
- [Moser-Tardos theorem: the resampling algorithm finds an assignment avoiding all events](moser-tardos-theorem.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
