# Strong normalization of CCω

Every well-typed term is strongly normalizing: if
$\Gamma \vdash t : A$ for some context $\Gamma$ and some term $A$, then $t$ is strongly
normalizing.

## Sources

- Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
