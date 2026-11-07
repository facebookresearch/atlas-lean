# Regular fractal sequence

A regular fractal sequence is a sequence $(x_n)_{n \ge 0}$ of
positive integers together with a position array $(p_i(j))_{i, j \ge 0}$ of natural numbers such
that: for every $i \ge 0$, the strictly increasing sequence $p_i(0) < p_i(1) < \cdots$ lists
exactly the positions $n$ with $x_n = i + 1$ (so every positive integer occurs infinitely often);
for all $i$ and $n$ with $x_n = i + 2$, some $m < n$ has $x_m = i + 1$; for all $h$, $i$ and $j$
with $h < i$, exactly one $k$ satisfies $p_i(j) < p_h(k) < p_i(j + 1)$; and for every $j$,
$p_i(j)$ is strictly increasing in $i$.

Source JIS VOL25/Kimberling,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Kimberling/kimber16.tex>, lines 103–219;
concept `jis_term_9b50b937a4f55a665e8d81fb`.

Source positive value `i + 1` is represented directly as the natural `i + 1`,
and `pos i j` is the zero-based position of its `j`-th occurrence.
