# Extending a bound-variable environment

For a value $v \subseteq \mathbb{N}$ and a valuation $bs : \mathbb{N} \to P(\omega)$ of de Bruijn indices, $v \cdot bs$ sends index $0$ to $v$ and index $n + 1$ to $bs(n)$. It is the valuation under one more binder, with the new bound variable valued by $v$.

## Background

- [Denotation of an untyped λ-term in the graph model](denote.md): where it is used.
