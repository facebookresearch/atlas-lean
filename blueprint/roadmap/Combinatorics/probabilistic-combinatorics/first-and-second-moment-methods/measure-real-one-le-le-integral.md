# First moment method

Let $\mu$ be a finite measure and $X$ an integrable real function with $X \ge 0$ almost
everywhere. Then

$$
\mu(\{X \ge 1\}) \le \int X \, d\mu .
$$

For a probability measure this is $\Pr[X \ge 1] \le \mathbb E X$; for a count $X$ with values in
$\mathbb N$ it reads $\Pr[X \neq 0] \le \mathbb E X$, so if $\mathbb E X \to 0$ along a sequence of
random structures, then $X = 0$ with high probability. This is Markov's inequality at level $1$,
and it gives the lower half of every threshold, for example $p \ll 1/n$ for triangles in
$G(n, p)$.

## Background

- [Second moment method](measure-real-eq-zero-le-variance-div-sq.md): the matching tool for showing $X > 0$.

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, proof of Proposition 4.11.
