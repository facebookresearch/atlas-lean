# Thue–Morse words separate $\gamma$ from $b$

For the Thue–Morse words $t_n$ of length $2^n$, defined by $t_0 = \mathtt{a}$ and $t_{n+1} = t_n \overline{t_n}$, where the bar exchanges $\mathtt{a}$ and $\mathtt{b}$, the smallest bidirectional macro scheme has size $b(t_n) = \Theta(n)$, while $\gamma(t_n) = 4$. Therefore there are infinite families of strings with $\gamma = O(1)$ and $b = \Theta(\log N)$ for length $N$, so $\gamma$ and $b$ are not equivalent up to constant factors.

## Proof sketch

The upper bound uses the recursive structure $t_{n+1} = t_n\overline{t_n}$ to build macro schemes with $O(1)$ new phrases per level. The lower bound analyzes how the copy pointers of a valid macro scheme must resolve the distinct factors of $t_n$ at each of the $n$ dyadic scales, using overlap-freeness of Thue–Morse words to show that each scale requires a new phrase boundary.

## Depends on

- [String attractors](string-attractor.md)
- [Grammar size $g$ and bidirectional macro scheme size $b$](grammar-and-macro-measures.md)

## Proof depends on

- [Thue–Morse words have smallest attractors of size four](thue-morse-gamma.md)
- [Dictionary compressors induce string attractors](compressors-induce-attractors.md)

## Sources

- Hideo Bannai, Mitsuru Funakoshi, Tomohiro I, Dominik Köppl, Takuya Mieno, Takaaki Nishimoto, "A Separation of gamma and b via Thue-Morse Words", SPIRE (2021).
