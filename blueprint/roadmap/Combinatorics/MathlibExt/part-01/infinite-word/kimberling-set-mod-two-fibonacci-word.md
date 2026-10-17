---
article_id: af_6591c8ddd78971932e5175b2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.kimberling_set_mod_two_fibonacci_word
---

# Kimberling Fibonacci Word

Kimberling's theorem: `K₁` is the closure of `{1}` under `n ↦ 2n` and
`n ↦ 4n - 1`, `S` its increasing enumeration; dropping the first term,
`S` mod 2 is the infinite Fibonacci word (fixed point of `0 ↦ 01`,
`1 ↦ 0`), i.e. it agrees with every iterate-prefix `φ^k([false])`.

The source gives a third proof (via transducer construction) of the main
result of Kimberling (Kim00), also reproved in Allouche–Shallit (AllSha05).
`K` is pinned as the fold-closure: each element is reached from `1` by a
bit-list of doublings and `4x - 1` steps. `S` is pinned as the strictly
monotone enumeration of `K`; `w` reads `S(n+1) mod 2`, dropping the first
term; `φ` is the Fibonacci morphism on `Bool` (`false` = 0). Verified
computationally: the first 21 terms of `w` (i.e. `S` mod 2 after
dropping the first term) match the morphism fixed point `01001010…`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fib Morph](fibonacci-word/fib-morph.md)
- [Fib Morph append](fibonacci-word/fib-morph-append.md)
- [Fib Word](fibonacci-word/fib-word.md)
- [Fib Word add two](../words/fibonacci-factorization/fib-word-add-two.md)
- [Fib Word nested succ](fibonacci-word/fib-word-nested-succ.md)
- [Fib Word prefix](fibonacci-word/fib-word-prefix.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.KimberlingFibonacciWord](../../../../../sources/v2/MathlibExt.md)
- Tomi Kärki, Anne Lacroix, and Michel Rigo, "On the Recognizability of Self-Generating Sets," Journal of Integer Sequences 13 (2010), Article 10.2.2, Theorem (section Kimberling set and the Fibonacci word, label secKF), lines 710–714, https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex
