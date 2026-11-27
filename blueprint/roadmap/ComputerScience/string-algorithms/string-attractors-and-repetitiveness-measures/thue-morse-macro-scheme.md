# Thue–Morse words separate $\gamma$ from $b$

For the Thue–Morse words $t_n$ of length $2^n$, defined by $t_0 = \mathtt{a}$ and $t_{n+1} = t_n \overline{t_n}$, where the bar exchanges $\mathtt{a}$ and $\mathtt{b}$, the smallest bidirectional macro scheme has size exactly $b(t_n) = n + 2$ for every $n \ge 2$, while $\gamma(t_n) = 4$ for $n \ge 4$. Therefore there are infinite families of strings with $\gamma = O(1)$ and $b = \Theta(\log N)$ for length $N$, so $\gamma$ and $b$ are not equivalent up to constant factors; more generally, for every $\gamma \ge 4$ there are string families with attractor size $\gamma$ and $b = \Theta(\gamma\log(N/\gamma))$.

## Proof sketch

The upper bound is by induction with the morphism $\mu(\mathtt{a}) = \mathtt{ab}$, $\mu(\mathtt{b}) = \mathtt{ba}$, $t_{n+1} = \mu(t_n)$: apply $\mu$ to every phrase of a scheme for $t_n$, doubling sources, split the images of the two letter phrases, and merge two of the resulting letter phrases into one copied phrase, so each level adds exactly one phrase, starting from size $4$ for $t_2$. For the lower bound, from a valid scheme of size $k$ for $t_n$, $n \ge 5$, one builds a valid scheme of size at most $k - i$ for $t_{n-i}$ for some $1 \le i \le 3$, handling odd-length phrases in an amortized way using overlap-freeness; computer checks give $b(t_2), b(t_3), b(t_4) = 4, 5, 6$.

## Depends on

- [String attractors](string-attractor.md)
- [Grammar size $g$ and bidirectional macro scheme size $b$](grammar-and-macro-measures.md)

## Proof depends on

- [Thue–Morse words have smallest attractors of size four](thue-morse-gamma.md)
- [Dictionary compressors induce string attractors](compressors-induce-attractors.md)

## Sources

- Hideo Bannai, Mitsuru Funakoshi, Tomohiro I, Dominik Köppl, Takuya Mieno, Takaaki Nishimoto, "A Separation of gamma and b via Thue-Morse Words", SPIRE (2021).
