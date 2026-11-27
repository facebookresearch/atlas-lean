# Generalized relative entropy of k-word frequency profiles

**k-word profile.** For a sequence $s$ of length $m$ over an alphabet $\Omega$ (20 amino acids), let $w_{k,1},\dots,w_{k,n}$ ($n = |\Omega|^k$) enumerate all words of length $k$, and let $c(w)$ count the overlapping occurrences of $w$ found by a sliding window at positions $1,\dots,m-k+1$. The **$k$-word frequency vector** is

$$F^s_k = \big(f(w_{k,1}),\dots,f(w_{k,n})\big), \qquad f(w_{k,t}) = \frac{c(w_{k,t})}{m-k+1},$$

a probability vector on $\Omega^k$.

**Generalized relative entropy.** For sequences $X, Y$ with profiles $f^X, f^Y$,

$$\mathrm{gre}_k(X,Y) = \sum_{t=1}^n f(w^X_{k,t})\,\log_2\frac{2f(w^X_{k,t})}{f(w^X_{k,t}) + f(w^Y_{k,t})},$$

with the convention $0\log 0 = 0$.

**Proposition.**
1. Every summand satisfies $f(w^X_{k,t})\log_2\frac{2f(w^X_{k,t})}{f(w^X_{k,t})+f(w^Y_{k,t})} \le f(w^X_{k,t}) \le 1$; in particular $\mathrm{gre}_k$ is finite for all profiles, unlike the Kullback–Leibler divergence, which is infinite when $f^Y$ vanishes where $f^X$ does not.
2. $\mathrm{gre}_k(X,Y) = \mathrm{KL}\big(F^X_k \,\big\|\, \tfrac12(F^X_k + F^Y_k)\big) \ge 0$, so $\mathrm{gre}_k(X,Y) + \mathrm{gre}_k(Y,X)$ is twice the Jensen–Shannon divergence of the two profiles and lies in $[0,2]$, with equality to $0$ iff $F^X_k = F^Y_k$.

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Writing $\log_2\frac{2p}{p+q} = 1 + \log_2\frac{p}{p+q}$ and using $p/(p+q) \le 1$ gives part 1. Part 2 is the definition of relative entropy against the midpoint distribution $M = (P+Q)/2$; non-negativity follows from Jensen's inequality, and each relative entropy to $M$ is at most $1$ bit because $P \le 2M$. The symmetric form is therefore a bounded divergence that handles words absent from one sequence, which matters for short proteins at $k \ge 2$ where most of the $20^k$ words do not occur.

## Sources

- Q. Dai, T. Wang, "Comparison study on k-word statistical measures for protein: from sequence to 'sequence space'", BMC Bioinformatics 9 (2008) 394, Methods, Eqs (3)–(5) and (17)–(20), <https://doi.org/10.1186/1471-2105-9-394>, PMCID PMC2571980.
