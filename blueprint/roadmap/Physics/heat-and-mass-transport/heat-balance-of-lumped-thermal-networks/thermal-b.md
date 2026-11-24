# Thermal B

Input matrix `diagonal (1 / C) * [g0 | 1]` for the input `(Tout, P)`: the outside
temperature (column `Sum.inl ()`) enters zone `i` with gain `g0 i / C i`, and the heating
power of zone `j` (column `Sum.inr j`) enters zone `j` alone, with gain `1 / C j`.
Meaningful for `C i > 0`.
