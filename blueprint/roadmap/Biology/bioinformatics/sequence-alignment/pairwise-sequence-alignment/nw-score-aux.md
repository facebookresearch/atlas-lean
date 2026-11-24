# Fuel-bounded Needleman–Wunsch recursion

For integer substitution scores $\sigma$ and gap score $g$, define $N_n(x, y)$ for a natural number $n$ and sequences $x, y$ by

- $N_0(x, y) = 0$;
- $N_{n+1}(\text{empty}, \text{empty}) = 0$, $N_{n+1}(\text{empty}, y) = g\,|y|$ and $N_{n+1}(x, \text{empty}) = g\,|x|$;
- for letters $a, b$, $N_{n+1}(a x, b y) = \max\bigl(N_n(x, y) + \sigma(a, b),\ N_n(x, b y) + g,\ N_n(a x, y) + g\bigr)$.
