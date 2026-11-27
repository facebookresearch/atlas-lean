# Bounded decimal decoding is exact

For a list $d = (d_1, \dots, d_k)$ of characters and $n \in \mathbb{N}$, the bounded decimal decoder returns $n$ on $d$ if and only if $1 \le k \le 11$, every $d_i$ is one of the ASCII digits `0`–`9`, and

$$n = \sum_{i=1}^{k} v(d_i)\, 10^{\,k-i},$$

where $v(d_i) \in \{0, \dots, 9\}$ is the value of the digit $d_i$ (most significant digit first).
