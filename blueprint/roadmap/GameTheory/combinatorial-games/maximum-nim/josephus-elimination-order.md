# Josephus elimination order

For natural numbers $k$ and $n$, place $1, \dots, n$ in
order on a circle and repeatedly remove one entry. When $L$ entries remain and the current
position is $s$ (zero-based, initially $s = 0$), the entry at zero-based position
$i = (s + k - 1) \bmod L$ is removed, where the subtraction is truncated at $0$, and $i$ becomes
the current position, so the next count starts at the entry after the removed one. The
Josephus elimination order with step $k$ on the circle $1, \dots, n$ is the list of all $n$
entries in the order of their removal.

For $k \ge 1$ this is the classical process that removes every $k$-th remaining entry; the last
entry of the list is the survivor.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Section 3 (Josephus problem).
