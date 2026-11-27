# Gödel numbering of sentences of arithmetic

The Gödel number $\ulcorner \sigma \urcorner$ of a sentence $\sigma$ of the language of arithmetic is given by the pairing numbering

$$\ulcorner \bot \urcorner = 0, \quad \ulcorner t_1 = t_2 \urcorner = \bigl\langle 1, \langle \ulcorner t_1 \urcorner, \ulcorner t_2 \urcorner \rangle \bigr\rangle, \quad \ulcorner \varphi \to \psi \urcorner = \bigl\langle 2, \langle \ulcorner \varphi \urcorner, \ulcorner \psi \urcorner \rangle \bigr\rangle, \quad \ulcorner \forall x\, \varphi \urcorner = \langle 3, \ulcorner \varphi \urcorner \rangle,$$

with terms numbered by $\ulcorner x_i \urcorner = \langle 1, i \rangle$ for bound variables and $\ulcorner f(t_1, \dots, t_l) \urcorner = \langle 2, \langle \mathrm{codeFun}(f), \mathrm{code}(\ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner) \rangle \rangle$, where the function-symbol tags are $\mathrm{codeFun}(0) = 0$, $\mathrm{codeFun}(S) = 1$, $\mathrm{codeFun}(+) = 2$, $\mathrm{codeFun}(\times) = 3$ (so the closed term $0$ has code $\langle 2, \langle 0, 0 \rangle \rangle = 6$), $\mathrm{code}() = 0$ and $\mathrm{code}(y_0, \dots, y_l) = \langle \mathrm{code}(y_0, \dots, y_{l-1}), y_l \rangle$. The pairing function is $\langle a, b \rangle = b^2 + a$ if $a < b$ and $a^2 + a + b$ otherwise.
