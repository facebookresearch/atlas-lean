# Formula for the $2$-adic Hilbert symbol

Let $a, b \in \mathbb{Q}_2$ be nonzero, written
as $a = 2^\alpha u$ and $b = 2^\beta v$ with $\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of
$\mathbb{Z}_2$. Then the $2$-adic Hilbert symbol satisfies

$$(a, b)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\omega(v) + \beta\omega(u)},$$

where $\varepsilon(u)$ and $\omega(u)$ are the classes modulo $2$ of $(u - 1)/2$ and
$(u^2 - 1)/8$.

Here $\varepsilon(u) = (\bar u - 1)/2$ and $\omega(u) = (\bar u^2 - 1)/8$ are computed as natural
numbers from the representative $\bar u \in \{0, \dots, 7\}$ of $u$ modulo $8$, which has the
same classes, and $\alpha, \beta$ are taken in absolute value, which leaves the sign unchanged.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973, Chapter III, §1.2, Theorem 1, p. 20 (the case $p = 2$). Serre defines $(a, b) = 1$ by a nonzero zero of $z^2 - a x^2 - b y^2$; this agrees with the definition used here by `hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`.
