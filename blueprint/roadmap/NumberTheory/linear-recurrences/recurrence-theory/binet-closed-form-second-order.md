# Binet formula for second-order linear recurrences

Let $K$ be a field, let
$P, Q, \alpha, \beta \in K$ with $\alpha \ne \beta$, and suppose that $\alpha$ and $\beta$ are
both roots of $z^2 - Pz + Q$. If a sequence $u : \mathbb{N} \to K$ satisfies
$u_{n+2} = P u_{n+1} - Q u_n$ for all $n$, then for every natural number $n$,

$$u_n = \frac{(u_1 - \beta u_0)\alpha^n - (u_1 - \alpha u_0)\beta^n}{\alpha - \beta}.$$

## Sources

- Hongshen Chua, "A Study of Second-Order Linear Recurrence Sequences via Continuants," Journal of Integer Sequences 26 (2023), Article 23.8.8, Theorem [Binet's formula] (label Th:Binet_Formula), lines 270–274, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Chua2/chua13.tex>. Proves `Wanted` entry `binet_closed_form_second_order`.
