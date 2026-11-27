# Double Coverage algorithm on the line

The *Double Coverage* algorithm for $k$ servers on the line serves a request $r$ as follows. If $r$ lies to the left of all servers (respectively to the right), the leftmost (respectively rightmost) server moves to $r$. Otherwise let $a$ and $b$ be the servers immediately to the left and right of $r$, with $s_a \le r < s_b$ (no move if a server is at $r$); both move toward $r$ by the distance $\min(r - s_a, s_b - r)$, so one of them reaches $r$. When several servers share a position, only one of them moves.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- M. Chrobak, H. J. Karloff, T. H. Payne and S. Vishwanathan, "New Results on Server Problems", SIAM Journal on Discrete Mathematics 4(2), 1991.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
