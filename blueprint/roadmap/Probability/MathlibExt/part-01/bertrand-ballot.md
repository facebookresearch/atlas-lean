---
article_id: af_af92678ff065541d015ea51d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bertrand_ballot
---

# Bertrand Ballot

Bertrand's ballot theorem (statement `bertrand-ballot-s1`):
in an election with `p` votes for A and `q` votes for B with `p > q ≥ 1`, counted in
uniformly random order, the probability that A is always strictly ahead of B throughout
the count equals `(p - q) / (p + q)`, stated here by counting ballot sequences
(lattice paths): the number of favourable sequences times `(p + q)` equals
`(p - q)` times the total number `(p + q).choose q` of sequences.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.BertrandBallot](../../../../sources/v2/MathlibExt.md)
- *Bertrand's ballot theorem*, Wikipedia, https://en.wikipedia.org/wiki/Bertrand%27s_ballot_theorem.
