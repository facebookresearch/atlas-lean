---
article_id: af_48c61b22ab1a408210a964c6
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.higherOrderBernoulliNumber
---

# Higher Order Bernoulli Number

Higher-order Bernoulli number `B_n^(α) = B_n^(α)(0)`.

The generalized polynomial `B_n^(α)(x)` is given by the source exponential
generating function `∑ n = 0 to ∞ B_n^(α)(x) t^n / n! = (t / (e^t - 1))^α e^(t x)`.

This is an explicit implementation obligation for the JIS source below, with `α : ℂ`
and `n : ℕ`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NetoHigherOrderBernoulli](../../../../../sources/v2/MathlibExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex Definition span: lines 99-112, text_sha256 `0acb659f24f1fa6140d178c11f64ab833f8d8a20336d0828a32665f37f2b7951`. File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`.
