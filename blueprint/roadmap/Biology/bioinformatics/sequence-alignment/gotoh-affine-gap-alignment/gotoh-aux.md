# Fuel-bounded Gotoh recursion

For integer substitution scores $\sigma$ and gap scores $o, e$, define $G_n(x, y, p)$ for a natural number $n$, sequences $x, y$ and a [gap state](gap-state.md) $p$ by

- $G_0(x, y, p) = 0$ and $G_{n+1}(\text{empty}, \text{empty}, p) = 0$;
- $G_{n+1}(\text{empty}, b y, p) = \gamma(p, Y) + G_n(\text{empty}, y, Y)$ and $G_{n+1}(a x, \text{empty}, p) = \gamma(p, X) + G_n(x, \text{empty}, X)$;
- $G_{n+1}(a x, b y, p) = \max\bigl(\sigma(a, b) + G_n(x, y, \varnothing),\ \gamma(p, X) + G_n(x, b y, X),\ \gamma(p, Y) + G_n(a x, y, Y)\bigr)$,

where $\gamma$ is the [gap cost](gap-cost.md).
