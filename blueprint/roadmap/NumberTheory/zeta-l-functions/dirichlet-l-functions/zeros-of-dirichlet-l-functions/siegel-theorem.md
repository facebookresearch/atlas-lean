# Siegel's theorem

For every real $\varepsilon > 0$ there is a constant $c > 0$ such that

$$
|L(1, \chi)| \ge c \, q^{-\varepsilon}
$$

for every real ($\chi^2$ principal), primitive, non-principal Dirichlet character $\chi$ of
conductor $q$. For such $\chi$, $L(1, \chi)$ is a positive real number. The constant $c$ is
ineffective: the proof does not compute it.

The proof relates real zeros of $L(\cdot, \chi)$ near $1$ to small values of $L(1, \chi)$: a real
zero close to $1$ makes $L(1, \chi)$ small, by a bound for the derivative of $L(\cdot, \chi)$ near $1$,
and conversely a small value $L(1, \chi)$ gives a real zero close to $1$, through the non-negativity
of the coefficients of $\zeta(s) L(s, \chi)$. Comparing two distinct real primitive characters
through the coefficients of $\zeta(s) L(s, \chi) L(s, \chi') L(s, \chi\chi')$, a real zero of one
L-function close to $1$ gives a lower bound for $L(1, \chi')$ for every other real primitive
character $\chi'$. This gives the bound with an effective constant for all real primitive characters
but at most one; including that possible exception, using only that its value $L(1, \chi)$ is
positive, makes the constant ineffective.

## Sources

- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014), <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>, Theorem 62(i), in the form stated in the paragraph after it: "all but at most one" real primitive character may be replaced by "all" at the cost of an ineffective constant. Its proof uses Lemma 57 (an exceptional zero makes $L(1, \chi)$ small), Lemma 59 (a small $L(1, \chi)$ gives an exceptional zero), Exercises 58 and 60 (asymptotics for sums of the coefficients of $\zeta(s) L(s, \chi)$ and of the four-fold product) and Proposition 61 (repulsion).
