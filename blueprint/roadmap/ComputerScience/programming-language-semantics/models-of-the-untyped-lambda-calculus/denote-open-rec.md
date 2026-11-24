# Substitution lemma for opening

Let $\rho$ be a valuation of the free variables and $s$ a term whose denotation under $\rho$ does not depend on the bound-variable valuation, for instance a locally closed term. For every term $M$, index $i$ and valuation $bs$ of the bound variables, opening the bound variable $i$ of $M$ with $s$, written $\{i \to s\}M$ (each occurrence of the index $i + d$ under $d$ abstractions is replaced by $s$), denotes $M$ with index $i$ valued by the denotation of $s$:

$$[\![\{i \to s\}M]\!]_{\rho, bs} = [\![M]\!]_{\rho, bs[i \mapsto [\![s]\!]_{\rho, bs}]}.$$

This is the semantic counterpart of substitution, and the key lemma for the soundness of β.

## Background

- [Soundness of a β-contraction in the graph model](denote-eq-of-beta.md): where it is used.
