# Parity of Catalan numbers

For every natural number $n$, the $n$th Catalan number $C_n$
is odd if and only if $n = 2^a - 1$ for some natural number $a$.

## Sources

- Alon Regev, "The Central Component of a Triangulation", Journal of Integer Sequences 16 (2013), Article 13.4.1, theorem `oddcats`, lines 132–147 of <https://cs.uwaterloo.ca/journals/JIS/VOL16/Regev/regev4.tex>. This entry records the displayed theorem statement. Lines 85–88 define `C_n` with the standard indexing used by Mathlib's `catalan`, so no index shift is required. The natural subtraction in `2 ^ a - 1` is safe because `2 ^ a` is positive. No parallel Catalan definition is introduced.
