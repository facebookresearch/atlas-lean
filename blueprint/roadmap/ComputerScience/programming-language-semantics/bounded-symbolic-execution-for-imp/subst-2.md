# Substitution of a symbolic store into an IMP Boolean expression

Let $\sigma : \mathbb{N} \to \mathrm{AExp}$ assign an IMP arithmetic expression to each variable index. Substitution of $\sigma$ into a Boolean expression is defined by recursion: a truth value stays; $a_1 = a_2$ and $a_1 \le a_2$ become the same comparison of $a_1[\sigma]$ and $a_2[\sigma]$, the arithmetic substitutions; and $\neg b$ and $b_1 \wedge b_2$ become the negation and the conjunction of the substituted operands.
