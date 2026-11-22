# Instantiating a shifted term

For all terms $t$ and $s$ of the simply typed lambda calculus
with references, shift every free de Bruijn variable of $t$ up by one (rename by
$x \mapsto x + 1$), then instantiate the result with $s$, replacing variable $0$ by $s$ and
lowering every other variable $x + 1$ to $x$. The outcome is $t$.
