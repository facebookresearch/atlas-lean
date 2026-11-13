# Formal sequence from a seed triplet

Let $F$ be a field and $a, b, c \in F$. A sequence
$u : \mathbb{N} \to F$ is a formal sequence with seed triplet $(a, b, c)$ when $b \neq 0$,
$u_0 = a$, $u_1 = b$, $u_2 = c$, and for every $n \ge 0$

$$u_{n+2} = \alpha u_{n+1} - u_n + \beta,$$

where $\alpha = \frac{ab + bc + ca}{b^2} - 1$ and $\beta = \frac{b^2 - ac}{b}$ are the
coefficient and the constant term of the formal-sequence recurrence.

## Sources

- <https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
