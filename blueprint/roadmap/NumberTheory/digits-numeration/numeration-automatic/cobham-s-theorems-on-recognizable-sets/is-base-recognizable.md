# Sets recognizable in base k

For a natural number $k$, a set $S$ of natural numbers is
recognizable in base $k$ when $k \ge 2$ and some deterministic finite automaton with a nonempty
finite set of states, reading words of base-$k$ digits from the most significant digit, accepts a
word $w = d_1 d_2 \cdots d_m$ exactly when $w$ is canonical (empty, or with $d_1 \neq 0$) and its
value $\sum_{i=1}^{m} d_i k^{m-i}$ lies in $S$.
