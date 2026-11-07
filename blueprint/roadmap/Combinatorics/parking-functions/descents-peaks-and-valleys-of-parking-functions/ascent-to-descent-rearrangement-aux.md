# Fuel-bounded ascent-to-descent rearrangement

For a fuel $N \in \mathbb{N}$ and a word
$x = x_1 \cdots x_m$ over $\mathbb{N}$, the word $\nu_N(x)$ is defined by recursion on $N$:
$\nu_0(x) = x$, and $\nu_{N+1}(x) = x$ when $m \le 1$. For $m \ge 2$, let $A$ be the set of
positions of the least letter of $x$ and $B$ the set of positions of its greatest letter. If
$b \le a$ for all $a \in A$ and $b \in B$ (Case 1), put $i = \max A$ and $j = \min B$; then
$\nu_{N+1}(x) = \nu_N(x_1 \cdots x_{j-1})\, x_i\, \nu_N(x_{j+1} \cdots x_{i-1})\, x_j\,
\nu_N(x_{i+1} \cdots x_m)$. Otherwise (Case 2), let $i$ be the greatest $a \in A$ such that
$a < b$ for some $b \in B$, and $j$ the least $b \in B$ with $b > i$; then
$\nu_{N+1}(x) = \nu_N(x_1 \cdots x_{i-1})\, x_j\, \nu_N(x_{i+1} \cdots x_{j-1})\, x_i\,
\nu_N(x_{j+1} \cdots x_m)$.

Every recursive call is on a strictly shorter word, so fuel $N = m$ never runs out.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Definition `nu` (Section 2).
