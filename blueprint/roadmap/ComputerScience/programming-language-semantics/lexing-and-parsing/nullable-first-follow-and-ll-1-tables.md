# NULLABLE, FIRST, FOLLOW and LL(1) tables

For a reduced context-free grammar $G$ (every nonterminal is reachable from the start symbol and derives some terminal word) with an end marker, the sets $\mathrm{NULLABLE}$, $\mathrm{FIRST}(X)$ and $\mathrm{FOLLOW}(X)$ computed as least fixed points of their defining inclusions over the finite set of symbols agree with their derivation-based definitions: $X$ is nullable if and only if $X \Rightarrow^* \varepsilon$; $a \in \mathrm{FIRST}(X)$ if and only if $X \Rightarrow^* a\beta$ for some $\beta$; and $a \in \mathrm{FOLLOW}(X)$ if and only if $S\$ \Rightarrow^* \alpha X a \beta$ for some $\alpha, \beta$. The predictive parsing table built from these sets has no conflicts if and only if $G$ is LL(1).

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *ITP 2019*, LIPIcs 141, 2019
- A. V. Aho, M. S. Lam, R. Sethi and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Addison-Wesley, 2006
