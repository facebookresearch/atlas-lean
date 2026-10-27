---
article_id: af_7d47093decb808dbc07375c9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Coding.SingletonBound.singleton_bound
---

# Singleton Bound

A `q`-ary block code of length `n` and minimum distance at least `d` has at
most `q ^ (n - d + 1)` codewords.

This is the Singleton bound. The proof punctures the code to its first
`n - d + 1` coordinates: two codewords agreeing on all retained coordinates
can differ in at most the `d - 1` deleted coordinates, contradicting the
minimum-distance hypothesis, so puncturing is injective on the code and the
bound follows by counting the punctured words.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Coding.SingletonBound](../../../../../sources/v2/MathlibExt.md)
- R. C. Singleton, "Maximum distance q-nary codes", IEEE Transactions on Information Theory 10(2) (1964), 116–118, DOI 10.1109/TIT.1964.1053661.
