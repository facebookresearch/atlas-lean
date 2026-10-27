---
article_id: af_154de3923499c88c981f877b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.triple_factorization_of_dot_diagram
---

# Triple Factorization

Triple Factorization Theorem for the indicated Riordan arrays: a Riordan
matrix with dot diagram `[b+ε, λ+δ; 1, b, λ]` factors as `P_b * C_λ * F_{ε,δ}`.

Riordan multiplication is matrix multiplication with
`(g,f)*(h,l) = (g·h(f), l(f))`, lines 113–117; the dot-diagram recursions
`r_{n,0} = a_1·r_{n-1,0} + a_2·r_{n-1,1} + …` and
`r_{n,k} = b_0·r_{n-1,k-1} + b_1·r_{n-1,k} + b_2·r_{n-1,k+1} + …` are at
lines 124–138.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.TripleFactorization](../../../../../../sources/v2/MathlibExt.md)
- Naiomi T. Cameron and Asamoah Nkwanta, *On Some (Pseudo) Involutions in the Riordan Group*, Journal of Integer Sequences 8 (2005), Article 05.3.7, Triple Factorization theorem due to Peart and Woodson, line 339, reused in the proof at line 373, <https://cs.uwaterloo.ca/journals/JIS/VOL8/Cameron/cameron46.tex>.
