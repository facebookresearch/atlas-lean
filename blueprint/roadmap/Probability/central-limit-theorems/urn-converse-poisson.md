# Converse of Poisson's theorem for urns

Let $(\Omega, \mu)$ be a probability space, let
$(p_n)_{n \ge 0}$ be real numbers in $[0, 1]$, and let $(X_n)_{n \ge 0}$ be pairwise independent
measurable real random variables on $\Omega$ such that each $X_n$ almost surely takes only the
values $0$ and $1$, and $\mu(X_n = 1) = p_n$. Then for every real number $L$ and almost every
$\omega \in \Omega$: if $\frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega) \to L$ as $n \to \infty$, then
$\frac{1}{n} \sum_{i=0}^{n-1} p_i \to L$ as $n \to \infty$.

Here $X_n$ records one draw from the $n$-th of a sequence of urns of unknown composition, a white
ball as $1$ and a black ball as $0$, and $p_n$ is the probability of drawing a white ball from the
$n$-th urn. Only pairwise independence is assumed: for uncorrelated variables with uniformly
bounded variances the strong law of large numbers still holds.

## Sources

- S. Ulam, Problem 17 of the Scottish Book. The proof is Kolmogorov's strong law of large numbers for independent bounded variables (1933).
