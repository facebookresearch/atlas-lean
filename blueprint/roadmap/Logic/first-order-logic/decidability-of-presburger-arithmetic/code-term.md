# Gödel numbers of Presburger terms

Terms and formulas of the language of Presburger arithmetic ($0$, $S$, $+$, $<$, $=$) with no free variables and $n$ bound variables in scope use the variables $x_0, \dots, x_{n-1}$.

Such terms are numbered recursively by

$$\ulcorner x_i \urcorner = \langle 1, i \rangle, \qquad \ulcorner f(t_1, \dots, t_l) \urcorner = \bigl\langle 2, \langle \ulcorner f \urcorner, \mathrm{code}(\ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner) \rangle \bigr\rangle,$$

where $\ulcorner 0 \urcorner = 0$, $\ulcorner S \urcorner = 1$, $\ulcorner + \urcorner = 2$, and $\mathrm{code}() = 0$, $\mathrm{code}(y_0, \dots, y_l) = \langle \mathrm{code}(y_0, \dots, y_{l-1}), y_l \rangle$.

Here $\langle a, b \rangle$ is the pairing function on $\mathbb{N}$ given by $\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise; it is a bijection $\mathbb{N}^2 \to \mathbb{N}$.
