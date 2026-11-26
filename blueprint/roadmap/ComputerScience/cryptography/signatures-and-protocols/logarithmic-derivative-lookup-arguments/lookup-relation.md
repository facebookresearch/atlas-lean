# Lookup relations with multiplicities

Given a table $\mathbf{t}=(t_1,\dots,t_T)\in\mathbb{F}^{T}$ and a witness column $\mathbf{f}=(f_1,\dots,f_n)\in\mathbb{F}^{n}$, the *lookup relation* holds iff $\{f_1,\dots,f_n\}\subseteq\{t_1,\dots,t_T\}$ as sets. The *multiplicity vector* $\mathbf{m}\in\mathbb{F}^{T}$ records, for distinct table entries, $m_j=|\{i:f_i=t_j\}|$ (computed in $\mathbb{F}$). A *vector lookup* uses tuples $f_i,t_j\in\mathbb{F}^{k}$. A *lookup argument* is an argument of knowledge for this relation when $\mathbf{f}$ (and possibly $\mathbf{t}$) is committed.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)

## Sources

- Ulrich Haböck, "Multivariate Lookups Based on Logarithmic Derivatives", IACR ePrint 2022/1530 (2022).
- Ariel Gabizon, Zachary J. Williamson, "plookup: A Simplified Polynomial Protocol for Lookup Tables", IACR ePrint 2020/315 (2020).
