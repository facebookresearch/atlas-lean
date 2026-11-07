# Asymptotic for the sum of $2^{\omega(n)}$ over squareful $n$

Let $\omega(n)$ be the
number of distinct prime factors of $n$, and let $f(n) = 2^{\omega(n)}$ if $n$ is squareful
($n \ne 0$ and $p^2 \mid n$ for every prime $p \mid n$; so $f(1) = 1$) and $f(n) = 0$ otherwise.
There are real constants $C_1$, $C_2$, $C_3$, $C_4$, $c > 0$, $K$ and $x_0$ such that for every
real $x \ge x_0$,

$$\Bigl|\sum_{1 \le n \le x} f(n) - \bigl(C_1 x^{1/2} \log x + C_2 x^{1/2} +
C_3 x^{1/3} \log x + C_4 x^{1/3}\bigr)\Bigr| \le
K x^{1/4} \exp\Bigl(c \Bigl(\frac{\log x}{\log \log x}\Bigr)^{1/3}\Bigr).$$

The paper writes the coefficient as $c_\varepsilon$, "for some $c > 0$", after "let
$\varepsilon > 0$": a constant chosen after $\varepsilon$, not a product with an arbitrarily small
factor. Its proof (equations (28)–(30)) produces, with $T$ the height parameter of its contour,
the exponent $(4 + \varepsilon) c (\log T / \log \log T)^{1/3}$ with $\varepsilon$ small and
$c > 0$ the fixed constant of its contour shift to $\operatorname{Re} s = 1/4 - c/g(T)$, where
$g(T) = (\log T)^{2/3} (\log \log T)^{1/3}$, chosen in terms of the Vinogradov–Korobov
zero-free region and the bound for $1/\zeta$ there (its Lemmas 5 and 6), so the coefficient
stays bounded away from $0$ and the statement is one existential $c > 0$.

## Sources

- Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24 (2024), Article A110, Theorem 1 (`integers-2024-A110-thm-1`).
