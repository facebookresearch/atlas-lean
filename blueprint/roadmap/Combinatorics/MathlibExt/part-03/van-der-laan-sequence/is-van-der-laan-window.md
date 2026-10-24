---
article_id: af_30dc8fdde3925bcd5dbff62a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsVanDerLaanWindow
---

# Is Van Der Laan Window

Van der Laan window predicate (concept `jis_term_73e55616c68e02e09fa349b5`,
raw phrase rank 204 `laan sequence`, source
`/data/users/akiezun/jis_corpus/artifacts/a6b5613ec29d7f2bcc9e-nacin5.tex`
(SHA-256 `52008805cb731f6d0e329d46c8da38ea6055d8ced9031f7a81cf630ddd7b69a1`),
lines 92-96).

The source calls a non-negative sequence Van der Laan when, for every four
consecutive terms, the largest term equals the sum of the two smallest
(conjecture from the OEIS entry; only the predicate is formalized here).
This is a faithful total definition on naturals: the largest of four values
is their iterated `max`, and the sum of the two smallest is the minimum of
the six pair sums, which exactly represents the order-statistic statement
and handles repeated values.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.VanDerLaanSequence](../../../../../sources/v2/MathlibExt.md)
