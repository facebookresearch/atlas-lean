# Expected rarefied richness and sample coverage

**Model.** A community has $k$ potential species. Abundances in a survey region are independent Poisson counts, so conditional on a pooled sample of $n$ individuals the species counts $(N_1, \dots, N_k)$ are multinomial with relative abundances $p_1, \dots, p_k$ ($p_i > 0$, $\sum_i p_i = 1$). The **conditional richness** $S(n) = \sum_i \mathbf{1}(N_i > 0)$ counts observed species, $S_0(n) = k - S(n)$ the unobserved ones, and the species abundance distribution $S_j(n)$ counts species seen exactly $j$ times, with

$$E\,S_j(n) = \sum_{i=1}^k \binom{n}{j} p_i^j (1 - p_i)^{n-j}, \qquad E\,S(n) = k - E\,S_0(n).$$

**Proposition (rarefaction loss).** Subsampling the pooled sample from $n$ to $n - m$ individuals loses, in expectation,

$$E\,S(n) - E\,S(n - m) = \sum_{i=1}^k \big(1 - (1 - p_i)^m\big)(1 - p_i)^{n-m}$$

species; in the Poisson limit $n p_i \to \Lambda_i$ this is approximately $\sum_i (1 - e^{-m p_i}) e^{-(n-m)p_i}$. The same identity with $n - m$ replaced by $n + m$ gives extrapolation of the species accumulation curve.

**Corollary (coverage).** The coverage, the probability that the $n$-th individual belongs to a species already seen among the first $n - 1$, is

$$C(n) = 1 - \sum_{i=1}^k p_i (1 - p_i)^{n-1} = 1 - \frac{E\,S_1(n)}{n},$$

which, with the singleton count $s_1$ in place of $E\,S_1(n)$, gives the Good–Turing estimate $\hat C = 1 - s_1/n$.

Size-based rarefaction compares communities at the common sample size $n^* = \min_t n_t$; coverage-based rarefaction compares them at a common coverage $q$, using sample size $n_t^* = \lfloor C^{-1}(q) \rfloor$, which varies with $t$.

## Expansion

Each species is absent from a sample of size $n$ with probability $(1 - p_i)^n$, since its marginal count is binomial. The loss formula is the difference of these absence probabilities at sizes $n - m$ and $n$, summed over species. Taking $m = 1$ gives the coverage identity, because $p_i(1 - p_i)^{n-1}$ summed over $i$ equals $E\,S_1(n)/n$.

## Sources

- H. Shimadzu, *On species richness and rarefaction: size- and coverage-based techniques quantify different characteristics of richness change in biodiversity*, J. Math. Biol. 77 (2018), 1363–1381 (Definitions 1–3, Eqs. (3)–(12), Proposition 1, Examples 1–2). <https://doi.org/10.1007/s00285-018-1255-5> (PMCID: PMC6182778)
