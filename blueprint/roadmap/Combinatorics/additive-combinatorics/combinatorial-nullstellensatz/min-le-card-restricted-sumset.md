# Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune theorem)

If $p$ is a prime and $A$ a nonempty subset of $\mathbb{Z}_p$, then the
[restricted sumset](../sumsets-inverse-theorems/restricted-signed-sumsets/restricted-sumset.md) $2^{\wedge}A = \{a + a' : a, a' \in A,\ a \ne a'\}$ satisfies

$$|2^{\wedge}A| \ge \min(p, 2|A| - 3).$$

Natural-number subtraction makes the bound $0$ when $|A| = 1$, where the paper's $2|A| - 3$ is
negative. The bound is attained by arithmetic progressions: for example $A = \{0, 1, 2\} \subseteq \mathbb{Z}_7$ has restricted sums $\{1, 2, 3\}$.

Proof (Alon). After passing to a subset one may assume $2|A| - 3 \le p$. If the
restricted sumset had at most $m = 2|A| - 4$ elements, it would lie in a set $C$ of exactly $m$
elements, and $Q = (x_1 - x_0) \prod_{c \in C} (x_0 + x_1 - c)$ would vanish on
$A \times (A \setminus \{a\})$. The coefficient of $x_0^{|A|-1} x_1^{|A|-2}$ in $Q$ is
$\binom{m}{|A|-1} - \binom{m}{|A|-2} = -\mathrm{Cat}(|A| - 2)$, a Catalan number up to sign, which
$p$ does not divide because $m < p$, so the Combinatorial Nullstellensatz gives a point where $Q \ne 0$.

## Informally uses

- [Combinatorial Nullstellensatz, Theorem 1.2](exists-eval-ne-zero.md): the paper deduces the bound from its Theorem 4.1 (with $k = 1$, $A_0 = A$, $A_1 = A \setminus \{a\}$ and $h = x_1 - x_0$), whose proof applies Theorem 1.2 to $h(x_0, x_1) \prod_{c \in C} (x_0 + x_1 - c)$ for a set $C$ of size $m$ containing the restricted sumset; the needed coefficient is that of the top-degree part $(x_1 - x_0)(x_0 + x_1)^m$.

## Background

- [Dias da Silva–Hamidoune theorem](../sumsets-inverse-theorems/sumsets-with-at-least-r-distinct-terms/dias-da-silva-hamidoune.md): the general statement for sums of $h$ distinct elements, whose case $h = 2$ is this bound.
- [Cauchy–Davenport–Chowla theorem](../sumsets-inverse-theorems/cauchy-davenport-chowla.md): the unrestricted sumset bound $|A + B| \ge \min(p, |A| + |B| - 1)$ and its extension to composite moduli.

## Related topics

- [Dias da Silva–Hamidoune theorem for $h = 2$](dias-da-silva-hamidoune-two.md): the $h = 2$ instance of the general statement, derived from this bound.

## Sources

- Noga Alon, "Combinatorial Nullstellensatz", *Combin. Probab. Comput.* 8 (1999) 7–29, Theorem 4.3 (attributed to José António Dias da Silva and Yahya Ould Hamidoune, *Bull. London Math. Soc.* 26 (1994)), Theorem 4.1 and Proposition 4.2 with $k = 1$.
