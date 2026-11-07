# Typing the polymorphic identity

In the empty context, the polymorphic identity
$\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ has type
$\Pi (A : \mathrm{Prop}).\, \Pi (x : A).\, A$.

This is typable only because $\mathrm{Prop}$ is impredicative: a product over
$A : \mathrm{Prop}$ whose codomain is a proposition is again a proposition.

## Sources

- Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
