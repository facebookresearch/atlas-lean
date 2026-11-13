# Tikhomirov's Theorem A: smallest singular value of shifted Bernoulli matrices

Let
$0 < p \le 1/2$ and $\varepsilon > 0$, and write $\sigma_{\min}(A)$ for the smallest singular value
of a real square matrix $A$. There exist a natural number $N > 0$ and a real number $C > 0$ such
that for every $n \ge N$ the following holds. Let $B$ be a random $n \times n$ real matrix on a
probability space $(\Omega, P)$ whose $n^2$ entries are mutually independent and each equal to $1$
with probability $p$ and to $0$ with probability $1 - p$, and let $J$ be the $n \times n$ matrix
all of whose entries are $1$. Then for every $s \in [-1, 0]$ and every real $t > 0$,

$$P\bigl(\sigma_{\min}(B + sJ) \le t / \sqrt{n}\bigr) \le (1 - p + \varepsilon)^n + C t.$$

## Sources

- K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_random_bernoulli_matrices` of the lean-eval benchmark.
