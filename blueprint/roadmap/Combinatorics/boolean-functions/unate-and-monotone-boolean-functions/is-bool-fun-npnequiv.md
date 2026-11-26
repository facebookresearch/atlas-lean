# NPN-equivalence of Boolean functions

An $n$-variable Boolean function $f$ is
NPN-equivalent to $g$ when $g$ is obtained from $f$ by permuting the variables, negating some
of the inputs and possibly negating the output: there are a permutation $\sigma$ of
$\{1, \ldots, n\}$, a vector $a \in \{0,1\}^n$ and a bit $c \in \{0,1\}$ such that
$g(x) = f(x_{\sigma(1)} \oplus a_1, \ldots, x_{\sigma(n)} \oplus a_n) \oplus c$ for every
$x \in \{0,1\}^n$, where $\oplus$ is exclusive or.

## Sources

- Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer Sequences 28 (2025), Article 25.3.4, Proposition 14.
