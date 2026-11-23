# Fuel-bounded Smith–Waterman recursion

For integer substitution scores $\sigma$ and gap score $g$, define $F_n(x, y)$ by

- $F_0(x, y) = 0$;
- $F_{n+1}(\text{empty}, y) = 0$ and $F_{n+1}(x, \text{empty}) = 0$;
- for letters $a, b$, $F_{n+1}(a x, b y) = \max\bigl(0,\ F_n(x, y) + \sigma(a, b),\ F_n(x, b y) + g,\ F_n(a x, y) + g\bigr)$.
