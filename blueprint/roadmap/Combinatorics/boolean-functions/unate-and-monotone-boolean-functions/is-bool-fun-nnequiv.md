# NN-equivalence of Boolean functions

An $n$-variable Boolean function $f$ is
NN-equivalent to $g$ when $g$ is obtained from $f$ by negating some of the inputs and
possibly the output: there are $a \in \{0,1\}^n$ and $c \in \{0,1\}$ such that
$g(x) = f(x \oplus a) \oplus c$ for every $x \in \{0,1\}^n$, where $\oplus$ is exclusive or
(coordinatewise on vectors).

## Sources

- Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer Sequences 28 (2025), Article 25.3.4, Proposition 13.
