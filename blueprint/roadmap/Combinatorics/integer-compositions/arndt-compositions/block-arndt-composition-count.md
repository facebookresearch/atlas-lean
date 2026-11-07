# Number of $k$-block Arndt compositions

For $k \ge 1$ and $n, m \ge 0$, $a^{(k)}(n, m)$ is
the number of $k$-block Arndt compositions of $n$ with $m$ parts: sequences
$(c_0, \ldots, c_{m-1})$ of positive integers with $c_0 + \cdots + c_{m-1} = n$ that strictly
decrease inside each block of $k$ consecutive positions $ki, ki + 1, \ldots, ki + k - 1$ (the last
block may be shorter), that is, $c_i > c_{i+1}$ for every $i$ with $i + 1 < m$ and
$i \not\equiv k - 1 \pmod{k}$. For $k = 2$ these are the Arndt compositions.

The definition is meant for $k \ge 1$; its value at $k = 0$ has no combinatorial meaning.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Section 5 (definition of `k`-block Arndt compositions).
