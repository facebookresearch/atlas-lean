# Weighted Motzkin recurrence for the coefficients of a Jacobi fraction

Let $K$ be a ring,
let $a$, $\alpha$, $\beta$ be sequences in $K$ and let $\mu_0 \in K$. Suppose that $a$ has Jacobi
fraction data $(\alpha, \beta, \mu_0)$: there are power series $F_0, F_1, \dots$ over $K$ with
$\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and $(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$ for
every $i \ge 0$. Then there is an array $(M_{n,j})_{n, j \ge 0}$ in $K$ with $M_{0,0} = 1$ and,
for all $n, j \ge 0$, $M_{0,j+1} = 0$, $M_{n+1,0} = \alpha_0 M_{n,0} + \beta_1 M_{n,1}$ and
$M_{n+1,j+1} = M_{n,j} + \alpha_{j+1} M_{n,j+1} + \beta_{j+2} M_{n,j+2}$, such that
$a_n = \mu_0 M_{n,0}$ for every $n \ge 0$.

## Sources

- Paul Barry, *From Fibonacci to Robbins: Series Reversion and Hankel Transforms*, Journal of Integer Sequences 24 (2021), Article 21.10.2, lines 110–117, https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex. Source SHA-256 `9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`. Normalized line-span SHA-256 `a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`. Concept `jis_dep_heilermann_049f63eb`. Grounded `jis_grounded_049f63eb8aadf7377777a597`. Barry does not explicitly state this auxiliary tableau lemma; it is a coefficientwise bridge for the displayed fraction.
