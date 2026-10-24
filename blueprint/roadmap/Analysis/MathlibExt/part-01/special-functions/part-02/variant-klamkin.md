---
article_id: af_90573874bcc7353d643fe72f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.variant_Klamkin
---

# Klamkin Variant

Variant of Klamkin's identity as an infinite series.

The generalized binomial `C(a, b+k)` is rendered with Gamma functions. Abel assumes only
`a - b + 1 ∉ ℕ`; here `h_ab` excludes every integer value of `a - b`, since otherwise some
`Gamma (a - (b + k) + 1)` sits at a pole (value `0` in Lean) and the rendered summands vanish.

Proof: Rewrite the summand as an ordinary hypergeometric coefficient and apply Abel's
specialization of Gauss's formula (Abramowitz-Stegun 15.1.20), then simplify by Gamma recurrence.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Has Sum ordinary Hypergeometric Coefficient klamkin](../part-01/gauss-hypergeometric-summation-klamkin/has-sum-ordinary-hypergeometric-coeffici.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.KlamkinVariant](../../../../../../sources/v2/MathlibExt.md)
- Ulrich Abel, "A Short Proof of the Binomial Identities of Frisch and Klamkin," Journal of Integer Sequences 23 (2020), Article 20.7.1, Theorem (label theorem-variant-Klamkin), equation (Identity-variant-Klamkin), lines 210–218, https://cs.uwaterloo.ca/journals/JIS/VOL23/Abel/abel12.tex
