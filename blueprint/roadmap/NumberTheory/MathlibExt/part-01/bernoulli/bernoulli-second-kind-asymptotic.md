---
article_id: af_0bd97aa0b02751c1260b67b6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bernoulli_second_kind_asymptotic
---

# Bernoulli Second Kind Asymptotic

Asymptotic expansion of the Bernoulli numbers of the second kind.

The complete expansion in powers of `1 / log n` is rendered order by
order: for every `m`, the truncation error is little-o of
`1 / (n * (log n)^(m+2))`. The main term is Steffensen's approximation,
as noted in the source.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Watson Laplace Lemma](../../../../Analysis/MathlibExt/part-01/asymptotics/watson-laplace-integral-asymptotic.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKindAsymptotic](../../../../../sources/v2/MathlibExt.md)
- Gergő Nemes, "An Asymptotic Expansion for the Bernoulli Numbers of the Second Kind," Journal of Integer Sequences 14 (2011), Article 11.4.8, Theorem (label theorem), equations (eq1)–(eq2), lines 124–133, https://cs.uwaterloo.ca/journals/JIS/VOL14/Nemes/nemes4.tex
