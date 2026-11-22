# Crochemore's square-freeness test

Let $f$ map each letter of the three-letter alphabet
$\{a, b, c\}$ to a finite word over a set $T$, and extend $f$ to words by concatenation,
$f(x_1 \cdots x_n) = f(x_1) \cdots f(x_n)$. Then $f$ maps every square-free word over
$\{a, b, c\}$ to a square-free word if and only if it maps every square-free word over
$\{a, b, c\}$ of length at most $5$ to a square-free word.

A word is square-free when no factor has the form $uu$ with $u$ nonempty. No non-erasing
hypothesis is assumed: the image of a letter may be empty.

Proof: reduce erasing morphisms first, then apply Currie's synchronization
method to a shortest square occurrence and its shortest source-word cover.

## Sources

- James D. Currie, *Finite Test Sets for Morphisms That Are Squarefree on Some of Thue's Squarefree Ternary Words*, Journal of Integer Sequences 22 (2019), Article 19.8.2, Section 1 (discussion after Theorem 1, quoting Crochemore), https://cs.uwaterloo.ca/journals/JIS/VOL22/Currie/currie20.html
- Maxime Crochemore, *Sharp characterizations of squarefree morphisms*, Theoretical Computer Science 18 (1982), 221–226, DOI 10.1016/0304-3975(82)90023-8.
