---
article_id: af_f92cb9b24a3ff26bd38920fd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fibonacci_card_parity_alternating_avoiding_312_231
---

# Fibonacci PAPAvoidance

Parity-alternating permutations of `[n]` starting with an odd entry, equivalently
index-parity-preserving permutations, that avoid both classical patterns `312` and `231`
are counted by the Fibonacci numbers: with zero-based `Fin n`, parity preservation is
`(π i).val % 2 = i.val % 2`, a `312` occurrence at `i < j < k` has
`π j < π k < π i`, a `231` occurrence at `i < j < k` has `π k < π i < π j`,
and for positive `n` the cardinality of this finite set equals `Nat.fib n`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.FibonacciPAPAvoidance](../../../../../../sources/v2/MathlibExt.md)
- Per Alexandersson, Samuel Asefa Fufa, and Frether Getachew Kebede, "Pattern-Avoidance and Fuss–Catalan Numbers", Journal of Integer Sequences 26 (2023), Article 23.4.2, Proposition lines 1757-1759, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Getachew/get3.tex>.
