# Lipschitz error bound: output error at most $L$ times the input error

Let $E$ and $F$ be normed abelian groups (for example normed vector spaces) and let
$f : E \to F$ be Lipschitz with constant $L \ge 0$: $\|f(u) - f(v)\| \le L\, \|u - v\|$ for all
$u, v \in E$. Then for every point $x \in E$ and every input error $\delta \in E$,

$$\|f(x + \delta) - f(x)\| \le L\, \|\delta\| .$$

This is the Lipschitz condition at $u = x + \delta$ and $v = x$. It is a deterministic bound on
the output error, valid for every size of $\delta$, with no probability model and no
linearisation.
