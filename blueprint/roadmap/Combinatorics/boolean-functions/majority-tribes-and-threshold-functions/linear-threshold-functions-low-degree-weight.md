# Linear threshold functions have Fourier weight at least 1/2 up to degree one

If $f : \{-1,1\}^n \to \{-1,1\}$ and a nonzero real function $\ell$ of degree at most one satisfy $f(x)\ell(x) \ge 0$ for all $x$ (in particular for every linear threshold function $f = \mathrm{sgn}(\ell)$), then $\mathbf{W}^{\le 1}[f] = \sum_{|S| \le 1}\hat f(S)^2 \ge 1/2$. More generally every polynomial threshold function of degree at most $k$ has $\mathbf{W}^{\le k}[f] \ge e^{-2k}$, using the $L^1$–$L^2$ comparison $\|p\|_2 \le e^k\|p\|_1$ for degree-$k$ polynomials.

## Proof sketch

$\mathbb{E}[f\ell] = \mathbb{E}|\ell|$ and, by Cauchy–Schwarz, $\mathbb{E}[f\ell] = \sum_{|S| \le 1}\hat f(S)\hat\ell(S) \le \sqrt{\mathbf{W}^{\le 1}[f]}\,\|\ell\|_2$. For $\ell = a_0 + \sum_i a_ix_i$, an extra uniform sign $x_0$ gives $|\ell(x)| \overset{d}{=} |a_0x_0 + \sum_i a_ix_i|$, so the Khintchine–Kahane inequality yields $\|\ell\|_2 \le \sqrt2\,\|\ell\|_1$; since $\mathbb{E}|\ell| > 0$ this gives the bound $1/2$. For degree $k$ use $\|p\|_2 \le e^k\|p\|_1$ in the same way.

## Depends on

- [Linear threshold function](../majority-is-least-stable-conjecture/is-linear-threshold-function.md)
- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Polynomial threshold functions and sparsity](polynomial-threshold-functions.md)

## Proof depends on

- [Khintchine–Kahane inequality with the optimal constant](khintchine-kahane-inequality-optimal-constant.md)
- [Moment comparisons and tail bounds for low-degree functions](../low-degree-functions-on-the-cube/moment-comparisons-for-low-degree-functions.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
