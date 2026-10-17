---
article_id: af_9b19c68b04ceb4e69199f998
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.HilbertWaringWanted.hilbert_waring
---

# Hilbert Waring

For every `k ≥ 1` there exists `g : ℕ` such that every `n : ℕ` is a sum of `g` `k`th powers: `∃ x
: Fin g → ℕ, n = ∑ i, (x i) ^ k`. Source: D. Hilbert, Beweis für die Darstellbarkeit der ganzen
Zahlen durch eine feste Anzahl n-ter Potenzen (Waringsches Problem), Math. Ann. 67 (1909) 281–305;
textbook in Vaughan, The Hardy-Littlewood Method; general includes minimal g(k).

Proof: We follow Linnik's elementary route as presented in Tim Jameson's notes: a mean-value
estimate gives positive Schnirelmann density for a bounded power sumset, which is then an additive
basis of finite order by Schnirelmann's inequality.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists additive basis of pos schnirelmann Density](../../../Combinatorics/MathlibExt/part-03/schnirelmann/exists-additive-basis-of-pos-schnirelman.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.HilbertWaring](../../../../sources/v2/MathlibExt.md)
