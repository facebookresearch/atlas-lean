# The parity-change bound on real zeros is false

For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$, set $a_{n+1} = 0$, $\tilde c_0(f) = a_0^2$ and
$\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$, and let $v(f)$ be the
number of parity changes between consecutive terms of the increasing list of indices $k \le n$
with $\tilde c_k(f) > 0$. There is such an $f$ with $a_k > 0$ for all $0 \le k \le n$ whose number
of distinct real zeros exceeds $v(f)$.

Katkova, Shapiro and Vishnyakova (Sec. 5) disprove Conjecture 9 via iterated primitives $Q_n$ of
an explicit $Q_{15}$. Splitting the repeated root also refutes the distinct-zero reading used
here: $\prod_{j<23}(x+1+j/10^4)\,(38x^2-199x+363)$ has positive coefficients, 23 distinct real
zeros and $v = 21$.

## Sources

- Olga Katkova, Boris Shapiro and Anna Vishnyakova, In search of Newton-type inequalities, arXiv:2403.12200 (2024), https://arxiv.org/abs/2403.12200.
