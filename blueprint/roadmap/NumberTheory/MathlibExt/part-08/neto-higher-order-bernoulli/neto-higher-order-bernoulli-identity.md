---
article_id: af_63bb9d55e8266485fce9816d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.neto_higher_order_bernoulli_identity
---

# Neto higher order bernoulli identity

Neto identity for higher-order Bernoulli numbers from the JIS source below.

For `x : ℂ` simultaneously the order and scalar base, and `n ℓ : ℕ`, with
inclusive upper bounds `Finset.range (n + 1)` and `Finset.range (ℓ + 1)`,
natural exponents, and sign `(-1)^(n + ℓ)`.

Proof: The substitution coefficient formula makes both sides polynomial in the order. For natural
orders, the cited Bernoulli EGF gives the reflection identity, formal differentiation proves Neto's
formula, and equality on all natural complex points finishes the polynomial argument.

## Depends on

- [Higher Order Bernoulli Number](higher-order-bernoulli-number.md)

## Proof depends on

- [Higher Order Bernoulli Number nat](higher-order-bernoulli-number-nat.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NetoHigherOrderBernoulli](../../../../../sources/v2/MathlibExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex Identity span: lines 662-670, text_sha256 `06790ccab662e77ae848bda8ff92dac6a404d8b43042d433d80c6dd7b127c56f`. File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`.
