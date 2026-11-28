# Inverse-probability-weighted cell mean

Let $U$ be a finite population of $N$ units. For outcomes $y : U \to \mathbb{R}$, cell probabilities $\pi_{ic}$, a cell $c$ and an assignment $f : U \to \{0,1,2,3\}$, the inverse-probability-weighted (Horvitz–Thompson) cell mean is

$$\hat m_c(f) = \sum_{i : f(i) = c} \frac{y_i}{N \pi_{ic}},$$

which is $0$ for an empty realized cell (and uses $a/0 = 0$).

## Sources

- T. Dasgupta, N. S. Pillai and D. B. Rubin, "Causal inference from $2^K$ factorial designs using the potential outcomes model", arXiv:1211.2481, Section 3.1, equations (1) and (2).
- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without replacement from a finite universe", *Journal of the American Statistical Association* 47 (1952), 663–685.
