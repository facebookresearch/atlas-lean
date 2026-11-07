# A pebbling move removes exactly one pebble

Let $n, k \in \mathbb{N}$, let $a$ assign
$a(x) \in \mathbb{N}$ pebbles to each vertex $x \in \{0, \dots, n-1\}$, and let $i \ne j$ be
vertices with $a(i) \ge k + 1$. Then the pebbling step from $i$ to $j$, which removes $k + 1$
pebbles from $i$ and adds $k$ pebbles to $j$, gives a position $b$ with
$\sum_x b(x) + 1 = \sum_x a(x)$.

## Sources

- Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024), Article 24.5.8, Section 1 (definition of a `(k+1:k)`-pebbling move).
