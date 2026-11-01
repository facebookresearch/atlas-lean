---
article_id: af_f407ce162088a44b76ae68b9
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.bAryBinomialCoefficient
---

# B Ary Binomial Coefficient

The b-ary binomial coefficient: for a valid positional base `b` with `2 ≤ b`,
the finite product of ordinary binomial coefficients `Nat.choose n_l k_l` over the
zero-padded base-`b` digits `n_l` of `n` and `k_l` of `k` (via `Nat.digits b`),
i.e. `∏ l, (n_l.choose k_l)` where both digit lists are padded with zeros to their
maximum length. Lexical identity `jis_term_2cbaa34dfe110242e8240dcc`, semantic concept
`jis_sem_53a0802e644cb28ded12d432`, source statement IDs `jis_30db487b6c50b220112654bd`,
`jis_4bca8b14577e811b2884b0f6`, `jis_63c8aaa1ece1935494892283`, `jis_829c8289db89acb73a53c052`,
`jis_86db58debbc80e01008e85bc`, `jis_bf54256f54829f8681d7d1f4`, `jis_e9d8c5a51bab29e334605dbd`,
`jis_fdf241424325af62582196db`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryBinomialCoefficient](../../../../../../../sources/v2/MathlibExt.md)
