# Congruence of products over a partition with multiplicities divisible by $p^v$

Let $p$
be a prime, $A$ a commutative ring and $\mathfrak{a}$ a divided-power ideal of $A$. Let
$f, g : \mathbb{N} \to A$ satisfy $f_n - g_n \in \mathfrak{a}$ for every $n \ge 1$. For a
partition $\lambda = (\lambda_1, \dots, \lambda_k)$ of a natural number $m$, write
$f_\lambda = f_{\lambda_1} \cdots f_{\lambda_k}$ and
$g_\lambda = g_{\lambda_1} \cdots g_{\lambda_k}$. If $v$ is a natural number such that every part
of $\lambda$ occurs a multiple of $p^v$ times, then $f_\lambda - g_\lambda = p^v c$ for some
$c \in \mathfrak{a}$, that is, $f_\lambda \equiv g_\lambda \bmod p^v \mathfrak{a}$.

The paper takes $v = v_p(\lambda) = \min_i v_p(\lambda_i)$, which is false: for $p = 2$,
$\lambda = (2)$, $A = \mathbb{Z}_{(2)}$, $\mathfrak{a} = (2)$, $f_n = e_n(X^2 + 2)$ and
$g_n = e_n(X^2)$, where $e_n(P)$ is the $n$-th elementary symmetric function of the roots of $P$,
$f_n \equiv g_n \bmod 2$ for all $n$ but $f_2 - g_2 = 2 \notin 4\mathbb{Z}_{(2)}$. The paper's
proof writes $\lambda = \mu^{p^v}$ in the partition monoid, which uses the multiplicity condition
stated here. The paper's symmetric functions are abstracted to arbitrary sequences $f, g$, as the
statement only uses their values.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Corollary 26.
