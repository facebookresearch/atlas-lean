# Regular fractal sequence

A regular fractal sequence is a sequence $(x_n)_{n \ge 0}$ of
positive integers together with a position array $(p_i(j))_{i, j \ge 0}$ of natural numbers such
that: for every $i \ge 0$, the strictly increasing sequence $p_i(0) < p_i(1) < \cdots$ lists
exactly the positions $n$ with $x_n = i + 1$ (so every positive integer occurs infinitely often);
for all $i$ and $n$ with $x_n = i + 2$, some $m < n$ has $x_m = i + 1$; for all $h$, $i$ and $j$
with $h < i$, exactly one $k$ satisfies $p_i(j) < p_h(k) < p_i(j + 1)$; and for every $j$,
$p_i(j)$ is strictly increasing in $i$.

Here $p_i(j)$ is the position, counted from $0$, of the $j$-th occurrence (counted from $0$) of
the value $i + 1$.

## Sources

- Clark Kimberling, *Self-Containing Sequences, Fractal Sequences, Selection Functions, and Parasequences*, Journal of Integer Sequences 25 (2022), Article 22.2.1, Sections 3–5 (position arrays, regular sequences, and fractal sequences with conditions (F1)–(F3)), https://cs.uwaterloo.ca/journals/JIS/VOL25/Kimberling/kimber16.html
