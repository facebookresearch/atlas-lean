# Lower bound for Oesterlé's product

Let $v \ge 0$ be an integer and let $P$ be a finite set of primes with at most $v$ elements. Then

$$\prod_{p \in P} \left(1 - \frac{\lfloor 2\sqrt{p} \rfloor}{p + 1}\right) \ge \frac{1}{6}\, 2^{-v}.$$

Each factor lies in $(0, 1]$. It equals $\tfrac13$, $\tfrac14$, $\tfrac13$ and $\tfrac38$ for
$p = 2, 3, 5, 7$, and it is at least $\tfrac12$ for every prime $p \ge 11$. So the product is at
least $\tfrac13 \cdot \tfrac14 \cdot \tfrac13 \cdot \tfrac38 \cdot \left(\tfrac12\right)^{v-4}
= \tfrac16\, 2^{-v}$ when $v \ge 4$, and at least the product of the $v$ smallest of these four
values, which exceeds $\tfrac16\, 2^{-v}$, when $v < 4$.

## Sources

- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [proof of Proposition 2.6, p. 615](https://doi.org/10.1017/S0305004125101825), for $P$ the set of primes dividing a fundamental discriminant $D$ other than the largest, and $v = v_2(h(D))$.
- Joseph Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki, vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, p. 310–311, for the values at $p = 2, 3, 5, 7$ and the bound for $p \ge 11$, [https://www.numdam.org/item/SB_1983-1984__26__309_0/](https://www.numdam.org/item/SB_1983-1984__26__309_0/).
