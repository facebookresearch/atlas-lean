# Totals at which every pebbling game is an N-game

Let $G$ be a simple graph on the
vertices $0, \dots, n-1$ and let $k$ be a natural number. In the $(k+1:k)$-pebbling game on $G$,
a move removes $k+1$ pebbles from a vertex and adds $k$ pebbles to an adjacent vertex. This is
the set of natural numbers $m$ such that every position with $m$ pebbles in total (a number of
pebbles on each vertex, summing to $m$) is an N-position, that is, not a P-position.

The paper's $m^{(k+1:k)}(G)$ is the least element of this set when the set is nonempty, and
"$m^{(k+1:k)}(G)$ does not exist" means the set is empty. The paper takes $m$ positive; $0$ never
lies in the set, because the empty position is a P-position.

## Sources

- Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024), Article 24.5.8, Section 1 (definition of `m^{(k+1:k)}(G)`).
