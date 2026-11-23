# Initial-segment congruence for the odd product block

For natural numbers $l$ and $u$ write
$\operatorname{odpr}(l, u)$ for the product of the odd integers $j$ with $l \le j \le u$, and let
$h(m) = \operatorname{odpr}(2^{m-1}+1, 2^m-1)$. Let $m \ge 4$ and $B$ be natural numbers with
$m - 1 \le B \le 3m - 7$, and put $d = \lfloor (B + 4 - m)/2 \rfloor$, that is,
$d = 2 + \lfloor (B - m)/2 \rfloor$ (so $d = 1$ when $B = m - 1$). Then

$$
h(m) \equiv \operatorname{odpr}\bigl(2^{m-1}+1,\ 2^{m-1}+2^d-1\bigr)^{2^{m-1-d}} \pmod{2^B}.
$$

The paper prints the hypotheses $2 \le m - 1 \le B \le 3m - 7$, which also allow $(m, B) = (3, 2)$.
There $d = 1$, $h(3) = 35$ and the right-hand side is $5^2 = 25$, but $35 - 25 = 10$ is not
divisible by $4$. Requiring $m \ge 4$ removes exactly that case and keeps every other printed case.

## Sources

- Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer Sequences 29 (2026), Article 26.3.1, Theorem 4.
