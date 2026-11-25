# Egorov's theorem on the real line under integrable domination

Let $f : \mathbb{R} \to \mathbb{R}$ be any function and $f_n : \mathbb{R} \to \mathbb{R}$ Borel
measurable functions with $f_n(x) \to f(x)$ for almost every $x$. Suppose there is a Lebesgue
integrable $g$ with $|f_n(x)| \le g(x)$ for all $n$ and all $x$. Then for every $\varepsilon > 0$
there is a Borel set $E$ of Lebesgue measure less than $\varepsilon$ such that $f_n \to f$
uniformly on $\mathbb{R} \setminus E$.

## Idea

Egorov's theorem says that on a finite measure space almost-everywhere convergence is uniform
outside a set of arbitrarily small measure. On the real line this fails in general: the
indicators of $[n, \infty)$ tend to $0$ everywhere, but not uniformly outside any set of finite
measure. An integrable bound restores the conclusion. Choose a Borel function $\tilde g$ equal to $g$
almost everywhere, and remove a Borel null set containing the points where $f_n(x)$ does not
converge to $f(x)$ and the points where $g \ne \tilde g$. Then the set $\{\tilde g \ge \delta\}$
has finite measure by Markov's inequality; at the remaining points outside it, $|f_n|$ and $|f|$
are at most $\delta$, and on it the finite-measure theorem applies. Doing this for a sequence $\delta_k \to 0$, with exceptional sets of measures
$\varepsilon 2^{-k}$, gives the result.

## Statements

- [Egorov's theorem on the real line under integrable domination](exists-measure-lt-tendsto-uniformly-on-c.md)
