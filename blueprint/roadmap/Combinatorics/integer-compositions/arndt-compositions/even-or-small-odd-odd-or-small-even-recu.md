# Recurrences for even-or-small-odd and odd-or-small-even compositions

For natural
numbers $k$ and $n$, let $c^{2k+1}_e(n)$ be the number of compositions of $n$ in which every part
is even or at most $2k + 1$, and $c^{2k}_o(n)$ the number in which every part is odd or at most
$2k$. If $k \ge 1$ and $n \ge 3$, then

$$c^{2k+1}_e(n) = c^{2k+1}_e(n - 1) + 2c^{2k+1}_e(n - 2) - c^{2k+1}_e(n - 3 - 2k)$$

and

$$c^{2k}_o(n) = c^{2k}_o(n - 1) + 2c^{2k}_o(n - 2) - c^{2k}_o(n - 2 - 2k),$$

where the last term is read as $0$ when its argument is negative.

Both recurrences fail at $n = 2$.

## Sources

- Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26 (2026), Article A64, Corollary 1.
