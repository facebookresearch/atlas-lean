# Descent generating function of parking functions

Write a sequence of length $n$ as
$(a_1, \dots, a_n)$; its descents are the $j \in \{1, \dots, n-1\}$ with $a_j > a_{j+1}$, and
$\operatorname{des}$ is their number. A parking function $f$ of length $n$ is read as the sequence
$a_j = f(j-1) + 1$. Let $PF_n$ be the set of parking functions of length $n$, $PF^{\uparrow}_n$
the set of nondecreasing ones, and $d(n, j)$ the number of $\alpha \in PF_n$ with
$\operatorname{des}(\alpha) = j$. For every $n \ge 1$, in the polynomial ring $\mathbb{N}[y]$,

$$\sum_{\alpha \in PF_n} y^{\operatorname{des}(\alpha)} = \sum_{j=0}^{n-1} d(n, j)\, y^j =
\sum_{\beta \in PF^{\uparrow}_n} \sum_{\pi} y^{\operatorname{des}(\pi)},$$

where, for each $\beta$, $\pi$ runs over the rearrangements of $\beta$: the sequences of length
$n$ with the same multiset of entries as $\beta$.

The paper prints the middle sum from $j = 1$; it is read from $j = 0$ (at $n = 1$ the printed
middle sum is $0$ while the other two sides are $1$). At $n = 0$ the left side is $1$ and the
middle sum is empty, so $n \ge 1$ is assumed, as in the paper.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Theorems 1 and 2 (`jis-2024-24.8.6-thm-1`, `jis-2024-24.8.6-thm-2`).
