# Digit block of an expansion

Let $S$ be a finite set of integers, read as the positions of
the digits $1$ of an expansion with digits $d_i$, so $d_i = 1$ if $i \in S$ and $d_i = 0$
otherwise. For an integer $k$ and a finite word $w = w_0 w_1 \cdots w_{m-1}$ over the natural
numbers, $w$ occurs as a digit block of $S$ at position $k$ when the digits
$d_k d_{k-1} \cdots d_{k-m+1}$, read from the highest position down, are the letters of $w$: for
every $i < m$, $d_{k-i} = 1$ holds exactly when $w_i = 1$. A letter $1$ stands for the digit $1$
and any other letter for the digit $0$; the empty word occurs at every position.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Sections 6 and 7 (digit blocks `d_{m-1} ⋯ d_0` and `d_{-1} ⋯ d_{-m}`).
