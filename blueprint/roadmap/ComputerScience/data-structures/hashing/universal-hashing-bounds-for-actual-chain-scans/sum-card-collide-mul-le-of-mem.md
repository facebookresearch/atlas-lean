# Average collision count for a stored key

Let $(h_i)_{i \in s}$ be a universal family of functions from keys to $\{0, \dots, m - 1\}$, indexed by a finite nonempty set $s$ (so $m > 0$, and for distinct keys $x \ne y$ at most $|s| / m$ indices $i \in s$ satisfy $h_i(x) = h_i(y)$). Let $S$ be a finite set of keys and $k \in S$. Then

$$m \sum_{i \in s} \bigl|\{x \in S : h_i(x) = h_i(k)\}\bigr| \le |s| \bigl(m + (|S| - 1)\bigr):$$

on average over $s$, the bucket of $k$ holds $k$ itself and at most $(|S| - 1)/m$ other keys of $S$.
