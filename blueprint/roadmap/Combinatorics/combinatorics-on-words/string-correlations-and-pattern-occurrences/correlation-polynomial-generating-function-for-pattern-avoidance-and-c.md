# Correlation-polynomial generating function for pattern avoidance

For words $X, Y$, the correlation $XY$ is the binary string of the length of $X$ whose $i$-th bit is $1$ when $Y$, placed under $X$ starting at the $i$-th character of $X$, agrees with $X$ on their overlap; it is read as a polynomial $XY_z$ in $z$ with the leftmost bit most significant, and $AA$ is the autocorrelation of $A$. Thus $AA_z = \sum_r z^{r-1}$ over the lengths $r \in \{1, \dots, |A|\}$ for which the prefix of $A$ of length $r$ equals its suffix of length $r$. Let $A$ be a nonempty word, $|A| \ge 1$, over an alphabet of $q \ge 2$ letters, let $f(n)$ be the number of strings of length $n$ containing no occurrence of $A$, with $f(0) = 1$, and let $F(z) = \sum_{n \ge 0} f(n) z^{-n}$. Odlyzko (1985, equation (4.2)), presenting joint work with Guibas, proves

$$F(z) = \frac{z\, AA_z}{1 + (z - q)\, AA_z},$$

by solving the relations $(z - q)F(z) + zF_A(z) = z$ and $F(z) = zAA_zF_A(z)$ (equations (4.4a)–(4.4b)) for the generating function $F_A$ of strings that end with their first occurrence of $A$; he notes that the formula appears, in a different form, in earlier work of Solov'ev. For fair coin tossing the expected number of tosses until $A$ first appears is $F(2) = 2AA_2$ (Section 5.1), and for i.i.d. uniform letters from $q$ symbols the same argument gives $F(q) = q\,AA_q$; for example $6$ for the pattern $HH$, where $AA = 11$ and $AA_2 = 3$. For two distinct nonempty patterns $A \ne B$ of the same length $|A| = |B| \ge 1$ in Penney's game, with fair coin tossing (so neither pattern is a subword of the other and the game ends almost surely with exactly one of them), the odds that the player choosing $B$ wins are $(AA_2 - AB_2)/(BB_2 - BA_2)$ (equation (5.3)), a formula first proved by Conway.

## Depends on

- [Pattern match at an offset](../../../ComputerScience/string-algorithms/string-matching-problem/match-at.md): an occurrence of a pattern as a match at a starting offset
- [Independence of σ-fields, random variables and events](../../../Probability/foundations/independent-events-and-random-variables/independence/independence-sigma-fields.md): i.i.d. uniform letters

## Expansion

1. Definitions: correlations and autocorrelations of words and their polynomial readings (Section 3).
2. The relations (4.4a), from appending a letter, and (4.4b), from appending $A$ and locating its first occurrence.
3. Solving them for $F(z)$ and $F_A(z)$ (equations (4.2) and (4.5)).
4. The waiting-time corollary from $F(q) = \sum_n f(n)q^{-n} = \sum_n P(\text{no occurrence in the first } n \text{ letters})$.
5. The linear system for a reduced set of patterns (Theorem 4.1) and Conway's odds for Penney's game, from the system for two patterns (equations (5.1)–(5.3)).

## Sources

- A. M. Odlyzko, Enumeration of strings, in *Combinatorial Algorithms on Words*, A. Apostolico and Z. Galil (eds.), NATO ASI Series F12, Springer, 1985, 205–228, Sections 3–5. <https://doi.org/10.1007/978-3-642-82456-2_14>
- Original result: L. J. Guibas and A. M. Odlyzko, String overlaps, pattern matching, and nontransitive games, J. Combin. Theory Ser. A 30 (1981), 183–208. <https://doi.org/10.1016/0097-3165(81)90005-4> The generating function and the Penney's game analysis follow Odlyzko (1985), Sections 4 and 5.1.
