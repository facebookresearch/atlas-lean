# The Amadio–Cardelli subtyping algorithm

Represent a recursive type $\alpha$ by a root variable $\alpha^*$ and a *system in canonical form* $\varepsilon_\alpha$: a finite map from type variables to right-hand sides
that are $\bot$, $\top$, a variable outside the domain of the system, or an arrow $t_2 \to t_3$ between variables in the domain, whose solution is the tree expansion of
$\alpha$; the systems for $\alpha$ and $\beta$ use disjoint, freshly named domains. The algorithm derives judgments $\Sigma, \varepsilon \supset \alpha \le \beta$, where the *trail* $\Sigma$ is a finite set of assumptions $t \le s$ between
variables, by the rules

- $\Sigma, \varepsilon \supset t \le s$ if $t \le s \in \Sigma$; $\Sigma, \varepsilon \supset \bot \le \beta$; $\Sigma, \varepsilon \supset \alpha \le \top$; $\Sigma, \varepsilon \supset a \le a$ for a variable $a$ outside the domain of $\varepsilon$;
- $\Sigma, \varepsilon \supset \alpha \to \beta \le \alpha' \to \beta'$ if $\Sigma, \varepsilon \supset \alpha' \le \alpha$ and $\Sigma, \varepsilon \supset \beta \le \beta'$;
- $\Sigma, \varepsilon \supset t \le s$ if $\Sigma \cup \{t \le s\}, \varepsilon \supset \varepsilon(t) \le \varepsilon(s)$, for $t, s$ in the domain of $\varepsilon$.

An *initial goal* $\Sigma, \varepsilon \supset t \le s$ has root variables $t$ and $s$ in the disjoint domains of $\varepsilon = \varepsilon_1 \cup \varepsilon_2$ and no variable of $\Sigma$ in the domain
of $\varepsilon$. Starting from an initial goal, unfoldings stay synchronized: whenever one side of a goal is a variable in the domain of $\varepsilon$, so is the other, so the
last rule covers all cases. Applied backwards, with the assumption rule taking priority (and the $\bot$ axiom before the $\top$ axiom at $\bot \le \top$), the rules generate an *execution tree*, which is always finite, of depth of
the order of the product of the sizes of the two systems. The tree *succeeds* if every leaf is closed by one of the axioms (assumption, $\bot$, $\top$ or variable)
and fails if some leaf is a goal to which no rule applies. Write $\alpha \le_A \beta$ if the execution tree for the initial goal
$\emptyset, \varepsilon_\alpha \cup \varepsilon_\beta \supset \alpha^* \le \beta^*$ succeeds.

The algorithm is [sound and complete](correctness-of-the-amadio-cardelli-subtyping-algorithm.md) for the [tree ordering](tree-ordering-on-recursive-types.md).

## Depends on

- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)
- [Canonical forms and regular systems of equations](canonical-forms-and-regular-systems-of-equations.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.1 (canonical forms and systems of equations, 4.1.3 systems in canonical form), Section 4.2 (the rules, the initiality condition and the remark on synchronized expansion, execution trees, 4.2.2 termination and the order of the depth bound, and 4.2.3 success and the algorithm ordering).
