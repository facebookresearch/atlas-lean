# The 3-dissection of the generating function of 3-regular tripartitions

Let $T_3(n)$ be
the number of $3$-regular tripartitions of $n$, and for $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler product. Then, as integer power series in $q$,

$$
f_1^{11} f_2^4 f_3^3 f_6^6 \sum_{n \ge 0} T_3(3n) q^n =
f_2^6 f_3^{18} + 8q f_1^3 f_2^3 f_3^9 f_6^9 + 16q^2 f_1^6 f_6^{18},
$$



$$
f_1^{10} f_2^2 f_6^3 \sum_{n \ge 0} T_3(3n + 1) q^n = 3 f_2^3 f_3^{12} + 12q f_1^3 f_3^3 f_6^9
$$

and

$$
f_1^9 \sum_{n \ge 0} T_3(3n + 2) q^n = 9 f_3^9.
$$

Since each $f_k$ has constant term $1$ and so is invertible, these are the identities
$\sum T_3(3n) q^n = f_2^2 f_3^{15}/(f_1^{11} f_6^6) + 8q f_3^6 f_6^3/(f_1^8 f_2) +
16q^2 f_6^{12}/(f_1^5 f_2^4 f_3^3)$,
$\sum T_3(3n + 1) q^n = 3 f_2 f_3^{12}/(f_1^{10} f_6^3) + 12q f_3^3 f_6^6/(f_1^7 f_2^2)$ and
$\sum T_3(3n + 2) q^n = 9 f_3^9/f_1^9$ with the denominators cleared.

## Sources

- Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 4, eqs. (49)–(51) (`integers-2024-A86-thm-4`).
