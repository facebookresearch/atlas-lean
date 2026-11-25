# Truth of a CNF matrix under an assignment

Let $G$ be a group, $x : \mathbb{N} \to G$ an assignment of the variables $x_0, x_1, \dots$, and $m$ a matrix: a list of clauses, each a list of literals $(b, w)$ with $w$ a group word. The matrix holds under $x$ if every clause $c$ of $m$ contains a literal $(b, w)$ with

$$w(x) = 1 \iff b = \mathrm{true},$$

where $w(x)$ is the value of $w$ in $G$ under $x$. That is, every clause has a true literal, where $(\mathrm{true}, w)$ means $w = 1$ and $(\mathrm{false}, w)$ means $w \ne 1$.
