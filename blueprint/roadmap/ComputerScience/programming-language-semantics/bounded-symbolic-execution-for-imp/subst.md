# Substitution of a symbolic store into an IMP arithmetic expression

Let $\sigma : \mathbb{N} \to \mathrm{AExp}$ assign an IMP arithmetic expression to each variable index. Substitution of $\sigma$ into an arithmetic expression is defined by recursion: a constant stays, a variable $x$ becomes $\sigma(x)$, and $a_1 + a_2$, $a_1 - a_2$ and $a_1 \cdot a_2$ become the same operation applied to the substituted operands.
