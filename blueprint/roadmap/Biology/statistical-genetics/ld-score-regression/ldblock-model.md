# LD-block dependence model

Let $\mu$ be a measure on $\Omega$, $\chi_1, \dots, \chi_M$ real functions on $\Omega$ (the
statistics of $M$ markers), $K$ a natural number and $V$ a real number. An LD-block model for
$(\chi_j)$ with block size $K$ and variance bound $V$ consists of an LD block $b(j) \in \mathbb{N}$
for every marker $j$ such that

- every block has at most $K$ markers: $\#\{k : b(k) = b(j)\} \leq K$ for every $j$;
- $\chi_j$ and $\chi_k$ are independent under $\mu$ whenever $b(j) \neq b(k)$;
- every $\chi_j$ is square integrable, with $\operatorname{Var}(\chi_j) \leq V$ under $\mu$.

It extends the [LD-score model](model.md), which fixes only second moments of effects and noise, by
independence between blocks and a variance bound for the statistics, which involves fourth moments.
