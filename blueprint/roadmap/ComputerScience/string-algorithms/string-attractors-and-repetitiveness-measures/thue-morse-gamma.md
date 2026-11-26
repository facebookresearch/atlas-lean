# Thue–Morse words have smallest attractors of size four

Let $t_n$ be the $n$-th Thue–Morse word, of length $2^n$, defined by $t_0 = \mathtt{a}$ and $t_{n+1} = t_n \overline{t_n}$, where the bar exchanges $\mathtt{a}$ and $\mathtt{b}$. Then $\gamma(t_n) = 4$ for every $n \ge 4$. In contrast, the BWT of $t_n$ has $r(t_n) = \Theta(n) = \Theta(\log |t_n|)$ runs, so $\gamma$ can be exponentially smaller than $r$ in the logarithm of the length.

## Proof sketch

Kutsukake, Matsumoto, Nakashima, Inenaga, Bannai and Takeda exhibit four explicit positions, near the middle of $t_n$ at scales $2^{n-2}$ and $2^{n-3}$, and verify, using the overlap-freeness of Thue–Morse words and the recursive structure of their factors, that every factor of $t_n$ has an occurrence crossing one of them; a short case analysis rules out attractors of size three.

## Depends on

- [String attractors](string-attractor.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](bwt-run-count.md)

## Sources

- Kanaru Kutsukake, Takuya Matsumoto, Yuto Nakashima, Shunsuke Inenaga, Hideo Bannai, Masayuki Takeda, "On Repetitiveness Measures of Thue-Morse Words", SPIRE (2020).
