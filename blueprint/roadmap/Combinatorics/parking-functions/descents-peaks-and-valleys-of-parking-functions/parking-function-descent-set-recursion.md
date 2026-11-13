# Recursion for parking functions with a given descent set

The descent set of a word
$w = (w_1, \dots, w_\ell)$ is $\{i : 1 \le i \le \ell - 1,\ w_i > w_{i+1}\}$, and $d(J; n)$ denotes
the number of parking functions of length $n$ with descent set $J$. Let $n \in \mathbb{N}$, let
$I \subseteq \{1, \dots, n - 1\}$ be nonempty with largest element $m$, and let
$I^- = I \setminus \{m\}$. Then

$$d(I; n) = \sum_{\beta} \sum_{X} d_X(I^-) - d(I^-; n),$$

where $\beta$ runs over the nondecreasing parking functions of length $n$, $X$ runs over the
distinct sub-multisets of size $m$ of the multiset of entries of $\beta$, and $d_X(I^-)$ is the
number of words of length $m$ whose multiset of letters is $X$ and whose descent set is $I^-$.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorem 18 (`jis-2024-24.8.6-thm-18`).
