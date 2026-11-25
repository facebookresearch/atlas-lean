# Truth of a formula after substituting for the outermost bound variable

Let $L$ be a first-order language, $s$ an $L$-term with free variables in $\alpha$ and one bound
variable, and $\varphi$ a bounded $L$-formula with free variables in $\alpha$ and $m + 1$ bound
variables. Substitute $s$ for the bound variable $0$ in every term of the atomic subformulas of
$\varphi$, the bound variable of $s$ becoming the bound variable $0$. Let $M$ be an $L$-structure,
$v : \alpha \to M$ an assignment of the free variables, and $x_0, \dots, x_m \in M$ values of the
bound variables. The substituted formula holds in $M$ under $v$ and $x$ if and only if $\varphi$
holds with $x_0$ replaced by the value of $s$, where $s$ is evaluated under $v$ with its bound
variable set to $x_0$; the other bound variables keep their values.
