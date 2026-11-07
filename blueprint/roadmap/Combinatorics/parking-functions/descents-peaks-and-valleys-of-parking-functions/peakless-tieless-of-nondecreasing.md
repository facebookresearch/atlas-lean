# Tie-and-value map

Let $n \in \mathbb{N}$ and $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$.
The ties of $f$ are the positions $i \in \{1, \dots, n-1\}$ with $f(i-1) = f(i)$, and its values
are the elements of the image of $f$. Form the list of the ties in decreasing order followed by
the values in increasing order. Then $\varphi_n(f) : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is the
map whose value at $k$ is the entry of this list at position $k$ (counting from $0$), or $k$
itself if the list has at most $k$ entries.

For nondecreasing $f$ the list has exactly $n$ entries. In the paper's one-based notation,
$\varphi$ sends $\alpha = (a_1, \dots, a_n)$ to its tie set $\{j + 1 : a_j = a_{j+1}\}$ in
decreasing order followed by its value set in increasing order.

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, the function `φ` of Theorem 30 (`jis-2024-24.8.6-thm-30`), defined as in arXiv:2312.16786v1, Definition 4.2.
