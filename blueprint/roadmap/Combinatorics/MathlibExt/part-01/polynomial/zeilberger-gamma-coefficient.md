---
article_id: af_35311dcf41a35c5f8d436c66
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.zeilberger_gamma_coefficient
---

# Zeilberger Gamma

Zeilberger's lemma: extraction of `gamma k` from `h_n (x * c(x)^2) / c(x)^n`,
where `c` is the Catalan generating function.

Provenance: Paul Barry, "The γ-Vectors of Pascal-like Triangles Defined by
Riordan Arrays", Journal of Integer Sequences 22 (2019), Article 19.1.4,
Zeilberger's Lemma proposition lines 281–283,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry2/barry402.tex>.
The gamma-matrix setup and `h` notation use supporting lines 110–120; the
Catalan generating function `c(x) = (1 - sqrt (1 - 4 * x)) / (2 * x)` has
coefficients `C_n = (1 / (n + 1)) * choose (2 * n) n` (A000108).
The malformed recalled display at source line 275 printing `gamma_n` on both
sides is excluded; the correctly printed proposition with `h_n` on the left
is formalized.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Polynomial.ZeilbergerGamma](../../../../../sources/v2/MathlibExt.md)
