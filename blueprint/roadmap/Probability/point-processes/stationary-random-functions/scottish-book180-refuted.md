# Scottish Book Problem 180 fails

The claim of Scottish Book Problem 180 is false: there are a
probability space $(\Omega, \mu)$ carrying a measurable random variable uniformly distributed on
$[0, 1]$ and a stationary random function $v$ on $\Omega$ with every $v_t$ measurable, such that
no measurable random variable $A : \Omega \to \mathbb{R}$ uniformly distributed on $[0, 1]$ and no
map $\varphi : \mathbb{R} \to \Omega$ satisfy both $A(\varphi(\alpha)) = \alpha$ for every
$\alpha \in [0, 1]$ and, for all real $t_1 \ne t_2$, the independence of
$\alpha \mapsto v_{t_1}(\varphi(\alpha))$ and $\alpha \mapsto v_{t_2}(\varphi(\alpha))$ with
respect to Lebesgue measure on $[0, 1]$.

A counterexample is $\Omega = \mathbb{R}$ with $\mu$ Lebesgue measure restricted to $[0, 1]$, the
identity as uniform variable, and $v_t(\omega) = \omega - 1/2$ for every $t$, which is stationary
with $c = R(h) = 1/12$. If $A$ and $\varphi$ existed, $\varphi$ would be injective on $[0, 1]$,
while both functions in the independence condition equal $f(\alpha) = \varphi(\alpha) - 1/2$. A
function independent of itself is almost everywhere constant, and an injective function on
$[0, 1]$ is not. No non-degeneracy hypothesis is added, since the source asks for none.

## Sources

- J. Kampe de Feriet, Problem 180 of the Scottish Book, typescript PDF pp. 82-83, printed pp. 79-80; see the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
