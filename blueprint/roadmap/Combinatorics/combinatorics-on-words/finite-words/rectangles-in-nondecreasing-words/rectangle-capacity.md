# Number of $r \times s$ rectangles in a bargraph

Let $w = w_0 w_1 \cdots w_{m-1}$ be a word
of natural numbers, drawn as a bargraph whose column $i$ has height $w_i$. The number of
occurrences of an $r \times s$ rectangle (height $r$, width $s$) in $w$ is the number of pairs
$(i, y)$ of natural numbers with $i < m$, $i + s \le m$ and $y \le w_0 + \cdots + w_{m-1}$ such
that $y + r \le w_{i+j}$ for every $j < s$.

Here $(i, y)$ is the rectangle whose lower left cell is in column $i$ and row $y$, both counted
from $0$. For $s \ge 1$ the conditions $i < m$ and $y \le w_0 + \cdots + w_{m-1}$ follow from the
others; for $s = 0$ the count is $m(w_0 + \cdots + w_{m-1} + 1)$.

## Sources

- Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and Smirnov Words*, Journal of Integer Sequences 27 (2024), Article 24.8.4, Introduction and Figure 2.
