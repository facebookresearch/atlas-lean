# Typing the polymorphic identity applied to falsity

Write $\bot$ for
$\Pi (P : \mathrm{Prop}).\, P$. In the empty context, the application of the polymorphic
identity $\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ to $\bot$ has type
$\Pi (x : \bot).\, \bot$.

## Sources

- Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
