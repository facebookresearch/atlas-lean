# Inversion of the Burrows–Wheeler transform

Let $L$ be a list over a linearly ordered alphabet with a least letter $\bot$ adjoined. The
inversion of $L$ is the reverse of the $(|L| - 1)$-step inversion walk from row $0$: the letters
$L[r_0], L[r_1], \dots, L[r_{|L|-2}]$ with $r_0 = 0$ and $r_{i+1} = \mathrm{LF}(r_i)$, read in
reverse order (the empty list when $|L| \le 1$). When $L$ is the Burrows–Wheeler transform of a
text, row $0$ is the rotation that starts with the sentinel.
