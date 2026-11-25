# Bounded almost everywhere convergent sequences converge weakly in L^p

Let $1 < p < \infty$ and $q$ the conjugate exponent, $1/p + 1/q = 1$. If real functions $f$ and
$f_n$ in $L^p(\mathbb{R})$ satisfy $f_n \to f$ almost everywhere and
$\sup_n \|f_n\|_{L^p} < \infty$, then $f_n$ converges weakly to $f$: for every
$g \in L^q(\mathbb{R})$, $\int f_n g \, dx \to \int f g \, dx$.

## Idea

Almost-everywhere convergence and weak convergence are different modes, but a bound in $L^p$ links
them when $1 < p < \infty$. Bounded sequences in $L^p$ have weakly convergent subsequences, and
almost-everywhere convergence identifies every such weak limit as $f$, so the whole sequence
converges weakly to $f$. The statement fails for $p = 1$: the functions $n \mathbf{1}_{(0, 1/n)}$
tend to $0$ almost everywhere and have norm $1$, but $\int_0^1 n \mathbf{1}_{(0,1/n)} = 1$.

## Statements

- [Bounded almost everywhere convergent sequences in $L^p$, $1 < p < \infty$, converge weakly](tendsto-integral-mul-of-ae-tendsto-of-e.md)
- [Bounded a.e.-null sequences in $L^p(0,1)$ converge weakly to zero](tendsto-integral-mul-of-ae-tendsto-zero.md): a special case on $(0, 1)$ with limit $0$.
- [Lebesgue measure on $(0,1)$](i01.md): the measure of that special case.
