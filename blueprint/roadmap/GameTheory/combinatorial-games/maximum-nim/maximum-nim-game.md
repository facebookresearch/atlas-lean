# The Maximum Nim game

For a rule function $f : \mathbb{N} \to \mathbb{N}$, the Maximum Nim
game with rule $f$ is the impartial game whose positions are the pile sizes $x \in \mathbb{N}$, in
which the moves from $x$ go to $x - u$ for each $u$ with $1 \le u \le \min(f(x), x)$. The rank of
a position is the pile size itself, and the starting position is the empty pile $0$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Section 2.
