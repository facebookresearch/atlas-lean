# Nonattacking placements

Let $B$ be a board, that is, a finite set of squares
$(i, j) \in \mathbb{Z}^2$, let $M$ be a list of basic moves $v \in \mathbb{Z}^2$, and let $k$ be a
natural number. The nonattacking placements of $k$ pieces with basic moves $M$ on $B$ are the
$k$-element subsets $S \subseteq B$ such that for all distinct squares $p, q \in S$ and every
move $v \in M$, the difference $q - p$ is not parallel to $v$, that is,
$(q_1 - p_1) v_2 \ne (q_2 - p_2) v_1$.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1.
