# Canonical forms and regular systems of equations

A recursive type is in *canonical form* if every $\mu t.\, \gamma$ in it has $t$ free in $\gamma$ and $\gamma$ of the form $\alpha \to \beta$. A *regular system in canonical form* $\varepsilon$ is a
finite map from type variables to right-hand sides of the forms $\bot$, $\top$, a variable outside its domain, or $t_2 \to t_3$ with $t_2, t_3$ in its domain; such a system has a
unique solution in trees, assigning a tree to each variable of its domain, since the associated map on tuples of trees for the domain variables is a contraction
(each right-hand side is $\bot$, $\top$, a variable outside the domain, or an arrow, which is guarded). For a μ-free type $\alpha$, $\mathrm{Sol}(\alpha, \varepsilon)$ is the tree of
$\alpha$ with each variable of the domain replaced by its solution; a recursive type is first translated into a root variable and a system, as in item 2.

1. Every recursive type $\alpha$ has a type $\beta$ in canonical form with the same [tree expansion](recursive-types-and-their-tree-expansions.md), $T\alpha = T\beta$; the key step is
   $T(\mu t.\, \mu s.\, \gamma[t, s]) = T(\mu v.\, \gamma[v, v])$.
2. There are maps $\alpha \mapsto \alpha^*$ (a root variable) and $\alpha \mapsto E\alpha$ (a regular system in canonical form) with $T\alpha = \mathrm{Sol}(\alpha^*, E\alpha)$ for every
   recursive type $\alpha$; conversely every regular system in canonical form and root variable determine a recursive type with the same solution.

## Depends on

- [Recursive types and their tree expansions](recursive-types-and-their-tree-expansions.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.1, the definition of canonical forms, Proposition 4.1.2 (existence of canonical forms), Sections 4.1.3–4.1.4 (regular systems and their solutions), Proposition 4.1.5 and Definition 4.1.6.
