# Gödel numbers of Presburger formulas

Terms and formulas of the language of Presburger arithmetic ($0$, $S$, $+$, $<$, $=$) with no free variables and $n$ bound variables in scope use the variables $x_0, \dots, x_{n-1}$.

Formulas built from $\bot$, equations, relation atoms, implication and universal quantification are numbered recursively by

$$\ulcorner \bot \urcorner = 0, \qquad \ulcorner t_1 = t_2 \urcorner = \bigl\langle 1, \langle \ulcorner t_1 \urcorner, \ulcorner t_2 \urcorner \rangle \bigr\rangle, \qquad \ulcorner t_1 < t_2 \urcorner = \bigl\langle 2, \langle 0, \mathrm{code}(\ulcorner t_1 \urcorner, \ulcorner t_2 \urcorner) \rangle \bigr\rangle,$$

$$\ulcorner \varphi \to \psi \urcorner = \bigl\langle 3, \langle \ulcorner \varphi \urcorner, \ulcorner \psi \urcorner \rangle \bigr\rangle, \qquad \ulcorner \forall x_n\, \varphi \urcorner = \langle 4, \ulcorner \varphi \urcorner \rangle,$$

where $0$ is the number of the relation symbol $<$, terms are numbered by $\ulcorner x_i \urcorner = \langle 1, i \rangle$ and $\ulcorner f(t_1, \dots, t_l) \urcorner = \langle 2, \langle \mathrm{codeFun}(f), \mathrm{code}(\ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner) \rangle \rangle$ with the function-symbol tags $\mathrm{codeFun}(0) = 0$, $\mathrm{codeFun}(S) = 1$, $\mathrm{codeFun}(+) = 2$ (so the closed term $0$ has code $\langle 2, \langle 0, 0 \rangle \rangle = 6$), tuples by $\mathrm{code}() = 0$, $\mathrm{code}(y_0, \dots, y_l) = \langle \mathrm{code}(y_0, \dots, y_{l-1}), y_l \rangle$, and in the quantifier case $\varphi$ has $n+1$ bound variables in scope.

A sentence (a formula with no bound variables in scope) receives the Gödel number of the case $n = 0$.

Here $\langle a, b \rangle$ is the pairing function on $\mathbb{N}$ given by $\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise; it is a bijection $\mathbb{N}^2 \to \mathbb{N}$.
