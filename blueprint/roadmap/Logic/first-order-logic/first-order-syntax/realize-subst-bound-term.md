# Value of a term after substituting for the outermost bound variable

Let $L$ be a first-order language, $s$ an $L$-term with free variables in $\alpha$ and one bound
variable, and $t$ an $L$-term with free variables in $\alpha$ and $m + 1$ bound variables
$0, \dots, m$. Substitute $s$ for the bound variable $0$ of $t$, the bound variable of $s$ becoming
the bound variable $0$ and every other variable of $t$ staying unchanged. Let $M$ be an
$L$-structure, $v : \alpha \to M$ an assignment of the free variables, and $x_0, \dots, x_m \in M$
values of the bound variables. The value of the substituted term under $v$ and $x$ is the value of
$t$ with $x_0$ replaced by the value of $s$, where $s$ is evaluated under $v$ with its bound variable
set to $x_0$; the other bound variables keep their values.
