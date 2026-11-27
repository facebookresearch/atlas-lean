# Thue–Morse words have smallest attractors of size four

Let $t_n$ be the $n$-th Thue–Morse word, of length $2^n$, defined by $t_0 = \mathtt{a}$ and $t_{n+1} = t_n \overline{t_n}$, where the bar exchanges $\mathtt{a}$ and $\mathtt{b}$; it is the $n$-th Thue–Morse block with $0, 1$ renamed $\mathtt{a}, \mathtt{b}$. Then $\gamma(t_n) = 4$ for every $n \ge 4$. In contrast, $z(t_n) = 2n$ for the self-referencing LZ77 factorization, and, by Brlek et al., the Burrows–Wheeler transform of $t_n$ taken over its cyclic rotations, without a sentinel, has exactly $2n$ runs for $n \ge 1$; both are $\Theta(\log|t_n|)$. With the appended sentinel used to define $r$ the run count is different (for $t_4$ it is $10$, not $8$). Also $\delta(t_n) = 10/(3 + 2^{4-n})$ for $n \ge 3$. So $\gamma = O(1)$ while $z$ and the number of runs of the cyclic Burrows–Wheeler transform are $\Theta(\log |t_n|)$.

## Proof sketch

Kutsukake, Matsumoto, Nakashima, Inenaga, Bannai and Takeda show that $K_n = \{2^{n-2}, 3\cdot 2^{n-3}, 2^{n-1}, 3\cdot 2^{n-2}\}$ is an attractor of $t_n$ for $n \ge 4$: taking the lowest common ancestor of its endpoints in the binary tree of the decomposition $t_{k+1} = t_k\overline{t_k}$, every factor has an occurrence containing the centre of some word of $N_n = \{t_{n-1}\overline{t_{n-1}}\} \cup \{t_k\overline{t_k}, \overline{t_k}t_k : k \le n-2\}$; occurrences of $t_{n-1}\overline{t_{n-1}}$, $t_{n-2}\overline{t_{n-2}}$, $\overline{t_{n-2}}t_{n-2}$ and $t_{n-3}\overline{t_{n-3}}$ are centred at the four positions, and each such word of order $k$ contains one of order $k-2$ with the same centre, so by induction every word of $N_n$ has an occurrence centred in $K_n$. For the lower bound, Brlek's formula for the number of distinct factors gives $\delta(t_n) > 3$ for $n \ge 6$, so $\gamma(t_n) \ge \lceil\delta(t_n)\rceil = 4$, and $n = 4, 5$ are checked by exhaustive search.

## Depends on

- [String attractors](string-attractor.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](bwt-run-count.md)
- [Size $z$ of the greedy LZ77 factorization](lz77-factorization-size.md)
- [Substring complexity $\delta$](substring-complexity.md)
- [Thue–Morse blocks](../../../Combinatorics/combinatorics-on-words/morphic-sturmian-words/thue-morse-sequence-and-its-generalizations/thue-morse-block.md)

## Proof depends on

- [Substring complexity is at most the attractor size](delta-at-most-gamma.md)

## Sources

- Kanaru Kutsukake, Takuya Matsumoto, Yuto Nakashima, Shunsuke Inenaga, Hideo Bannai, Masayuki Takeda, "On Repetitiveness Measures of Thue-Morse Words", SPIRE (2020), arXiv:2005.09524.
- Srečko Brlek, Andrea Frosini, Ilaria Mancini, Elisa Pergola, Simone Rinaldi, "Burrows-Wheeler Transform of Words Defined by Morphisms", IWOCA (2019).
