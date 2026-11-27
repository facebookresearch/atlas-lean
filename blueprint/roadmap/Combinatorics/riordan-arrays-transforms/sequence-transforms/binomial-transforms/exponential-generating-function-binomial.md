# Exponential generating function of the binomial transform

Let $(a_n)_{n \ge 0}$ and
$(b_n)_{n \ge 0}$ be real sequences with $b_n = \sum_{k=0}^{n} \binom{n}{k} a_k$ for every $n$,
and let $A : \mathbb{R} \to \mathbb{R}$ be any function. For every real number $t$, if the series
$\sum_{n \ge 0} a_n t^n / n!$ converges absolutely with sum $A(t)$, then the series
$\sum_{n \ge 0} b_n t^n / n!$ converges absolutely with sum $e^t A(t)$.

The formulation is pointwise: convergence of the exponential generating function of $a$ is
assumed only at the point $t$ under consideration.

## Sources

- Ayhan Dil, Veli Kurt, and Mehmet Cenkci, *Algorithms for Bernoulli and Related Polynomials*, Journal of Integer Sequences 10 (2007), Article 07.5.4, Proposition 1.2 (proof attributed to Seidel), with the binomial-transform relations (8) and (9), <https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.pdf>.
