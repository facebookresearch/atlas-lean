# A $(k+1:k)$-pebbling move

Let $a = (a_0, \dots, a_{n-1})$ be a distribution of pebbles on
the vertices $0, \dots, n-1$, let $k$ be a natural number and let $i$ and $j$ be vertices. The
position after the $(k+1:k)$-pebbling move from $i$ to $j$ is the distribution $b$ with
$b_j = a_j + k$, $b_i = a_i - (k + 1)$ if $i \ne j$, and $b_x = a_x$ for every other vertex $x$.
When $i \ne j$ and $a_i \ge k + 1$, this removes $k + 1$ pebbles from $i$ and adds $k$ pebbles
to $j$.

Subtraction is truncated at $0$, so $b_i = 0$ when $i \ne j$ and $a_i < k + 1$.

## Sources

- Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024), Article 24.5.8, Section 1 (definition of a `(k+1:k)`-pebbling move).
