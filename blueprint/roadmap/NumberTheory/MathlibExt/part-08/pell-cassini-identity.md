---
article_id: af_b2fe93a0823e51b85a3a5e4d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pell_cassini_identity
---

# Pell Cassini Identity

Cassini's identity for Pell numbers: `P (k-1) * P (k+1) = P k ^ 2 + (-1)^k`
for `k ≥ 1`, with the Pell sequence abstracted by its initial values and
recurrence; the casts to `ℤ` carry the signs.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PellCassiniIdentity](../../../../sources/v2/MathlibExt.md)
- aBa Mbirika, Janee Schrader, and Jürgen Spilker, "Pell and Associated Pell Braid Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and Related Numbers," Journal of Integer Sequences 26 (2023), Article 23.6.4, Lemma (label lem:Cassini_identity_Pell_version), lines 367–369, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.tex>; attributed there to Horadam, Identity (30). Proves `Wanted` entry `pell_cassini_identity`.
