# A Cole–Vishkin step shrinks the palette

In one Cole–Vishkin step, a node of color $x$ whose successor has color $y \ne x$ takes the new color $2i + b$, where $i$ is the least bit position at which $x$ and $y$ differ and $b$ is bit $i$ of $x$. If $x, y < 2^k$ with $k \ge 1$, the new color is less than $2k$.

## Sources

- R. Cole and U. Vishkin, "Deterministic coin tossing with applications to optimal parallel list ranking", *Information and Control* 70 (1986), 32-53.
