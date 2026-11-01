---
article_id: af_a112679f8a302fe77e49e64c
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.squares_aaabb_classification
---

# Squares Aaabb Classification Wanted

Classification of squares of the form aa...ab...b: the only squares whose
decimal representation is a block of `r ≥ 1` copies of digit `a` followed by
a block of `s ≥ 1` copies of digit `b` are the trivial infinite families
`10 ^ (2 * i)`, `4 * 10 ^ (2 * i)`, `9 * 10 ^ (2 * i)` together with
16, 25, 36, 49, 64, 81, 144, 225, 441, 1444 and 7744.

`Nat.digits 10 n` is little-endian, so the `b`-block comes first; the
hypothesis `1 ≤ a ≤ 9`, `b ≤ 9` matches the proof setup at lines 292–296.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Digits.SquaresAaabbClassificationWanted](../../../../../sources/v2/WantedExt.md)
- Omar Kihel and Florian Luca, "Perfect Powers With All Equal Digits But One," Journal of Integer Sequences 8 (2005), Article 05.5.7, Theorem (label thm:3), lines 273–279, https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.tex
