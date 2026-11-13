# Flicking valleyless-tieless parking functions

Identify a parking function $f$ of length
$m$ with the word $(f(0) + 1, \dots, f(m-1) + 1)$. A word $(a_1, \dots, a_m)$ has a tie if
$a_k = a_{k+1}$ for some $k$, a peak if $a_{k-1} < a_k > a_{k+1}$ for some $k$, and a valley if
$a_{k-1} > a_k < a_{k+1}$ for some $k$. For $1 \le i \le m$, let
$\mathrm{flick}_i(x_1, \dots, x_m) = (x_i, x_{i-1}, \dots, x_1, x_m, x_{m-1}, \dots, x_{i+1})$,
the block $x_m, \dots, x_{i+1}$ being empty when $i = m$. Let $D$ be the set of parking
functions $(a_1, \dots, a_{n+1})$ with no valleys and no ties such that $a_1 = 1$ and
$a_{n+1} > 1$, and let $\varphi$ send $v \in D$ to $\mathrm{flick}_i(v)$, where $i$ is the
position of the strictly largest entry of $v$. Then $\varphi$ is a bijection from $D$ onto the
set of parking functions $(b_1, \dots, b_{n+1})$ with no peaks and no ties such that
$b_1 > b_{n+1}$.

The paper's domain condition $a_{i+1} > 1$ is a typo for $a_{n+1} > 1$, its domain in the same
display.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Proposition 37 (`jis-2024-24.8.6-prop-37`).
