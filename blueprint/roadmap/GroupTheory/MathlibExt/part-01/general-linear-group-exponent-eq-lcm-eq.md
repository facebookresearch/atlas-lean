---
article_id: af_4671d938313a8f64f12b6c9f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalLinearGroup_exponent_eq_lcm_eq_cyclotomicProduct
---

# General Linear Group Exponent

Exponent of `GL(m, 𝔽_p)` as a `p`-power times an lcm, equivalently a
cyclotomic product.

`Nat.clog p m` is `⌈log_p m⌉`; the lcm runs over `p^1 - 1, …, p^m - 1` and
the product over `Φ_1(p)⋯Φ_m(p)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GroupTheory.GeneralLinearGroupExponent](../../../../sources/v2/MathlibExt.md)
- Eugene Karolinsky and Dmytro Seliutin, *Carmichael Numbers for GL(m)*, Journal of Integer Sequences 23 (2020), Article 20.10.6, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Karolinsky/kar2.tex>, Theorem `fermat_matr` (quoting J. B. Marshall, *On the extension of Fermat's theorem to matrices of order n*, Proc. Edinb. Math. Soc. 6 (1939), and I. Niven, *Fermat's theorem for matrices*, Duke Math. J. 15 (1948)), lines 139-144; the lcm/cyclotomic identity is the paper's Proposition, lines 113-118.
