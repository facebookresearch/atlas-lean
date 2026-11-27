# IMP small-step relation

The single-step relation $\to$ on IMP configurations is the
smallest relation satisfying the following rules, for all variables $x$, arithmetic expressions
$a$, Boolean expressions $b$, commands $c, c_1, c_1', c_2$ and states $\sigma, \sigma'$.
Assignment: $(x := a, \sigma) \to (\mathtt{skip}, \sigma[x \mapsto v])$, where $v$ is the value
of $a$ in $\sigma$. Sequencing: $(\mathtt{skip}; c_2, \sigma) \to (c_2, \sigma)$, and if
$(c_1, \sigma) \to (c_1', \sigma')$ then $(c_1; c_2, \sigma) \to (c_1'; c_2, \sigma')$.
Conditional: $(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, \sigma)$ steps to
$(c_1, \sigma)$ if $b$ evaluates to true in $\sigma$ and to $(c_2, \sigma)$ if it evaluates to
false. Loop: $(\mathtt{while}\ b\ \mathtt{do}\ c, \sigma)$ steps to $(W, \sigma)$, where $W$ is
the command $\mathtt{if}\ b\ \mathtt{then}\ (c; \mathtt{while}\ b\ \mathtt{do}\ c)$
$\mathtt{else}\ \mathtt{skip}$.
