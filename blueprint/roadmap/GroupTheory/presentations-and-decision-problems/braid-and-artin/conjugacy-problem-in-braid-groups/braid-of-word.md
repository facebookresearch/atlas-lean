# The braid represented by a word in the Artin generators

Let $n \ge 2$ and let $B_n$ be the [braid group on $n$ strands](../endomorphisms-of-braid-groups/braid-group.md), realized as the Artin group of the Coxeter matrix of type $A_{n-1}$, with standard generators $\sigma_1, \dots, \sigma_{n-1}$. A word in these generators is a finite sequence of letters $(i, \varepsilon)$ with $i \in \{1, \dots, n - 1\}$ and $\varepsilon \in \{+1, -1\}$. The braid represented by the word $(i_1, \varepsilon_1), \dots, (i_k, \varepsilon_k)$ is the product

$$\sigma_{i_1}^{\varepsilon_1} \sigma_{i_2}^{\varepsilon_2} \cdots \sigma_{i_k}^{\varepsilon_k}$$

in $B_n$, and the empty word represents the identity. For $n \le 1$ there are no generators, and the only word is the empty word.

The same braid is the image of the word, read as an element of the free group on $\sigma_1, \dots, \sigma_{n-1}$, as in [the braid represented by a braid word](../conjugators-in-braid-groups/braid-of.md).
