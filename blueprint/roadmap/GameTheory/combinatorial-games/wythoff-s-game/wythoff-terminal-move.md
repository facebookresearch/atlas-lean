# Moves of Wythoff's game with terminal positions

Let $\ell$ be a natural number. In the
game $K^\ell$, whose positions are pairs $(x, y)$ of natural numbers (the sizes of two piles of
tokens), there is a move from $(x, y)$ to $(x', y')$ when $x + y > \ell$ and either $y' = y$ and
$x' < x$, or $x' = x$ and $y' < y$, or $x = x' + k$ and $y = y' + k$ for some $k > 0$. Thus the
positions with $x + y \le \ell$ are terminal, and from any other position a move removes a
positive number of tokens from one pile, or the same positive number from both piles.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, the game `K^ℓ` of Theorem 17 (`jis-2026-26.1.6-thm-17`): Wythoff's moves with terminal positions `{(x, y) | x + y ≤ ℓ}`.
