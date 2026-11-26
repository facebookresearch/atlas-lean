# The low-degree algorithm as a statistical query learner

Under the uniform distribution on $\{0,1\}^n$, for each set $T$ of at most $t$ coordinates let $\chi_T$ be the $\pm 1$ character and query $(x, y) \mapsto y^{\pm}\chi_T(x)$, whose expectation is the Fourier coefficient $\hat{c}(T)$ of the target read as a $\pm 1$ function. The low-degree algorithm asks these $N = \sum_{j \le t}\binom{n}{j}$ queries non-adaptively with tolerance $\tau$ and outputs the sign of $\sum_{|T| \le t} a_T \chi_T$ for the answers $a_T$. If every concept in $C$ has Fourier weight $\sum_{|T| > t}\hat{c}(T)^2 \le \kappa$, the algorithm learns $C$ with error at most $N\tau^2 + \kappa$. In particular the parities on at most $t$ coordinates are learned with error $N\tau^2$.

## Proof sketch

The error of the sign of an approximation $p$ is at most $\mathbb{E}[(c - p)^2]$, and by Parseval this equals the squared estimation errors of the $N$ low coefficients, at most $N\tau^2$, plus the high-degree weight $\kappa$.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)
- [Fourier coefficient on the Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Fourier coefficient on the Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- N. Linial, Y. Mansour and N. Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM, 1993.
- M. Kearns, "Efficient Noise-Tolerant Learning from Statistical Queries", Journal of the ACM, 1998.
