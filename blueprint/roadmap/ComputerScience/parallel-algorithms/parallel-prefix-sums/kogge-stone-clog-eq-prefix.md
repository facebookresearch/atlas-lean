# The scan computes all prefixes in logarithmically many rounds

Let $x_0, x_1, \dots$ be a
sequence in a monoid $M$ and let $n$ be a natural number. After $\lceil \log_2 n \rceil$ rounds of
the Kogge–Stone scan (the least $K$ with $n \le 2^K$), every position $i < n$ holds the prefix
product $x_0 x_1 \cdots x_i$.
