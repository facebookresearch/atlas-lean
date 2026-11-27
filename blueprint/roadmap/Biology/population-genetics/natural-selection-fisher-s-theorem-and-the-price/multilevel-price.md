# Multilevel Price equation

Let a finite population be divided into finitely many groups $k$, group $k$ having a finite set of
$n_k$ members $j$, with population size $N = \sum_k n_k$ and group weights $q_k = n_k / N$
proportional to group size. Each individual $(k, j)$ has fitness $w_{kj}$, trait $z_{kj}$ and mean
offspring trait $z'_{kj}$ (all real), and $W_k$, $Z_k$ are the averages of $w$ and $z$ over the
members of group $k$. If the total fitness $\sum w$ over all individuals is nonzero, then

$$
\bar w \Bigl(\frac{\sum w z'}{\sum w} - \bar z\Bigr) =
\sum_k q_k \Bigl(W_k - \sum_l q_l W_l\Bigr)\Bigl(Z_k - \sum_l q_l Z_l\Bigr) +
\sum_k q_k\, \mathbb{E}_j\bigl[(w_{kj} - W_k)(z_{kj} - Z_k)\bigr] +
\mathbb{E}\bigl[w\,(z' - z)\bigr],
$$

where $\bar w$, $\bar z$ and $\mathbb{E}$ are averages over the whole population and
$\mathbb{E}_j$ averages over the members of group $k$. In words, $\bar w\, \Delta \bar z$ is the
between-group covariance $\mathrm{Cov}_k(W_k, Z_k)$, plus the mean within-group covariance
$\mathrm{E}_k[\mathrm{Cov}_j(w_{kj}, z_{kj})]$, plus the transmission term $\mathrm{E}[w (z' - z)]$,
with population moments and groups weighted by size. The fitnesses may have any sign; no other
hypothesis is needed. The hypothesis $\sum w \ne 0$ makes the population nonempty, $N > 0$, but
groups may be empty: an empty group $k$ has $q_k = 0$, and $W_k$, $Z_k$ and its within-group
average are $0$, an average over no members being $0$.
