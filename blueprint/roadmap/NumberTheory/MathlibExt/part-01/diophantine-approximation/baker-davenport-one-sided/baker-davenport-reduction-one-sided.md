---
article_id: af_58a93ac59833a722f8f13f08
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bakerDavenport_reduction_oneSided
---

# Baker Davenport reduction one Sided

One-sided Baker–Davenport reduction lemma.

Concept `jis_rank27_baker_davenport_one_sided`, semantic id
`jis_grounded_3d649f47290c78b9a73677c9`.

Here `|x - round x|` formalizes distance to the nearest integer, and this
declaration is the one-sided form from the cited lemma: the final linear form
`(u : ℝ) * γ - (v : ℝ) + μ` appears with one-sided strict inequalities and no
absolute-value bars.
It follows from `bakerDavenport_reduction_oneSided_general`. The hypotheses `hN`, `hγ`
and `hq`, and the positivity conditions on `u`, `v` and `w`, are unused and keep the source's
shape; `hqN` only supplies `0 < q`.
Proves `Wanted` entry `bakerDavenport_reduction_oneSided`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Baker Davenport reduction one Sided general](baker-davenport-reduction-one-sided-gene.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DiophantineApproximation.BakerDavenportOneSided](../../../../../../sources/v2/MathlibExt.md)
- Bilizimbéyé Edjeou, Amadou Tall, and Mohamed Ben Fraj Ben Maaouia, "Powers of Two as Sums of Three Lucas Numbers," Journal of Integer Sequences 23 (2020), Article 20.8.8, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Edjeou/edj4.tex>, exact source span: Lemma `lem1`, lines 200–211. Source-file SHA-256 `ef293eb1fb3bec15a47898830b7ed2ea8c38ca4c491750d5a197cb16e00125fc`; exact-span SHA-256 `e8df3e4bbefc3b0825b721bcff7f5d918b3006429e63ee4b1d902ffce1f606d7`.
