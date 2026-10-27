---
article_id: af_f844a681fd5ba78aee633717
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.fineNumber
---

# Fine Number

Fine numbers (OEIS A000957), zero-based: `fineNumber n` is source `𝔽_(n+1)`.

Source explicit formula `𝔽_n = (1/n) * ∑_{i=1}^n (-2)^(i-1) * i * C(2n, n-i)`
with `𝔽_1 = 1`, from JIS VOL21/Janjic3/janjic96.tex lines 105-108 and 157-158.
Phrase concept `jis_term_dfac4b97dfaf92729d46eb23`; source statement
`jis_5d8bd849271ecf8ace5bbc6f`; source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL21/Janjic3/janjic96.tex`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.FineNumber](../../../../../sources/v2/MathlibExt.md)
