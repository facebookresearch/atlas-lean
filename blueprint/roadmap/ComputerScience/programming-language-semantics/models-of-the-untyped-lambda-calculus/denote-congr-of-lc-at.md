# Denotations depend only on the bound variables in scope

Let $M$ be a term all of whose bound indices are below $k$, in the sense that every occurrence of a bound index $i$ under $d$ abstractions of $M$ has $i < k + d$. If two valuations $bs$ and $bs'$ of the bound variables agree on $0, \ldots, k - 1$, then $[\![M]\!]_{\rho, bs} = [\![M]\!]_{\rho, bs'}$ for every valuation $\rho$ of the free variables: the denotation of $M$ depends only on $bs(0), \ldots, bs(k-1)$.

## Background

- [Locally closed terms ignore the bound-variable environment](denote-congr-of-lc.md): the case $k = 0$.
