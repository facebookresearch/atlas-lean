---
article_id: af_3157207295dcae52547cdf64
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generating_function_term_extraction
---

# Generating Function Term Extraction

A sequence term is recovered from its generating function via
`t N = floor (c ^ (N^2) * f (c ^ -N)) mod c ^ N` under the growth and convergence
hypotheses (convergence stated as summability of the series at `c ^ -N`).

Provenance: M. Prunescu and J. M. Shunia, "On Modular Representations of
C-Recursive Integer Sequences", Journal of Integer Sequences 28 (2025),
Article 25.5.3, Theorem `ThmExtraction1`, source lines 169–173,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Prunescu/prunescu3.tex>.
The paper attributes the result to Prunescu and Sauras-Altuzarra.
Only the first representation (for `N ≥ m ≥ 2` with `t j < c ^ (j - 2)`)
is recorded, not the `c ≥ 8` variant for all `n ≥ 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Sequences.GeneratingFunctionTermExtraction](../../../../../sources/v2/MathlibExt.md)
