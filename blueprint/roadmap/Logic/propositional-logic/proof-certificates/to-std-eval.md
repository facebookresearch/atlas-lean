# Translation to the standard CNF format preserves satisfaction

For every assignment $v$ of Boolean values to the natural-number variables and every CNF formula
$\varphi$, the translation of $\varphi$ into the standard CNF format evaluates to true under $v$
exactly when $v$ satisfies $\varphi$. Variables are kept unchanged and literal polarity is
preserved; the empty clause is false and the empty formula is true.
