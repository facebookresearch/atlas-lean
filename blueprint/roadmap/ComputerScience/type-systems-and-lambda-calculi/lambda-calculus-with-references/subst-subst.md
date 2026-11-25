# Composition of substitutions in the lambda calculus with references

For all parallel
substitutions $\sigma, \tau$, each sending every de Bruijn index to a term of the simply typed
lambda calculus with references, and every term $t$, applying $\sigma$ to $t$ and then $\tau$ to
the result gives the same term as applying to $t$ the substitution that sends each index $x$ to
the result of applying $\tau$ to $\sigma(x)$.
