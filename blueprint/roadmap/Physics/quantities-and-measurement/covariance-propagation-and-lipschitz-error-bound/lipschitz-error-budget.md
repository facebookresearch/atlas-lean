# Lipschitz error budget: output error at most $L$ times the input bound

Let $E$ and $F$ be normed abelian groups and let $f : E \to F$ be Lipschitz with constant
$L \ge 0$: $\|f(u) - f(v)\| \le L\, \|u - v\|$ for all $u, v \in E$. If $x, \delta \in E$ and a
real number $\varepsilon$ satisfy $\|\delta\| \le \varepsilon$, then

$$\|f(x + \delta) - f(x)\| \le L\, \varepsilon .$$

So an input error budget $\varepsilon$ gives the output error budget $L\varepsilon$; it follows
from the [Lipschitz error bound](lipschitz-error-propagation.md) $L\|\delta\|$ because $L \ge 0$.
The hypothesis $\|\delta\| \le \varepsilon$ forces $\varepsilon \ge 0$.
