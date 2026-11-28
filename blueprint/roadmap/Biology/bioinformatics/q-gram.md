# The $q$-gram of a word at an offset

For a word $x = x_0 x_1 \cdots x_{w-1}$ of length $w$ and an offset $i$ with $0 \le i \le w - q$, the $q$-gram of $x$
at $i$ is the window $x_i x_{i+1} \cdots x_{i+q-1}$ of length $q$, as a word indexed by $\{0, \dots, q - 1\}$. There
are $w - q + 1$ offsets when $q \le w$ and none when $q > w$.
