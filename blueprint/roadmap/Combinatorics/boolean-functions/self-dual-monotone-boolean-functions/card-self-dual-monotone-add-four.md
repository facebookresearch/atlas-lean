# Counting self-dual monotone functions on $n + 4$ variables

Let $D_n$ be the set of
monotone Boolean functions on $n$ variables, ordered pointwise, with $\lor$ the pointwise
disjunction and $f^*$ the dual of $f$. For $x, h \in D_n$ let $\mathrm{re}(x, h)$ be the number
of $z \in D_n$ with $x \le z \le h$. Then the number of self-dual monotone Boolean functions on
$n + 4$ variables equals

$$
\sum_{a, b, c \in D_n} \ \sum_{h \in D_n,\ h \ge a \lor b \lor c \lor a^* \lor b^* \lor c^*}
\mathrm{re}(a \lor b \lor c, h) \, \mathrm{re}(a \lor b^* \lor c^*, h) \,
\mathrm{re}(b \lor a^* \lor c^*, h) \, \mathrm{re}(c \lor a^* \lor b^*, h).
$$

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 13 (`jis-2025-25.6.5-thm-13`).
