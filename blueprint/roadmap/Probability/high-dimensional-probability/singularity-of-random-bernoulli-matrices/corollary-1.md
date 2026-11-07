# Singularity probability of Bernoulli matrices

Let $0 < p \le 1/2$. For each $n$, let $B_n$ be
a random $n \times n$ real matrix on a probability space $(\Omega_n, P_n)$ whose $n^2$ entries are
mutually independent and each equal to $1$ with probability $p$ and to $0$ with probability $1 - p$.
Then there is a function $o : \mathbb{N} \to \mathbb{R}$ with $o(n) \to 0$ as $n \to \infty$ such
that $P_n(\det B_n = 0) = (1 - p + o(n))^n$ for every $n \ge 1$.

## Sources

- K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-RandomBernoulliMatrices.lean Via leanprover/lean-eval@38361be, problem `annals_random_bernoulli_matrices`.
