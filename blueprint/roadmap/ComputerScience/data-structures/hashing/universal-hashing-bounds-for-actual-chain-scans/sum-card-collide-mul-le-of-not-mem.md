# Average collision count for an absent key

Let $(h_i)_{i \in s}$ be a universal family of functions from keys to $\{0, \dots, m - 1\}$, indexed by a finite nonempty set $s$ (so $m > 0$, and for distinct keys $x \ne y$ at most $|s| / m$ indices $i \in s$ satisfy $h_i(x) = h_i(y)$). Let $S$ be a finite set of keys and $k \notin S$. Then

$$m \sum_{i \in s} \bigl|\{x \in S : h_i(x) = h_i(k)\}\bigr| \le |s|\,|S|:$$

on average over $s$, at most $|S|/m$ keys of $S$ share the bucket of $k$.
