# Singularity probability of Rademacher matrices

For each $n$, let $M_n$ be a random
$n \times n$ real matrix on a probability space $(\Omega_n, P_n)$ whose $n^2$ entries are mutually
independent and each have the Rademacher law, with mass $1/2$ at each of $1$ and $-1$. Then there
is a function $o : \mathbb{N} \to \mathbb{R}$ with $o(n) \to 0$ as $n \to \infty$ such that
$P_n(\det M_n = 0) = (1/2 + o(n))^n$ for every $n \ge 1$.

## Sources

- K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_random_bernoulli_matrices` of the lean-eval benchmark.
