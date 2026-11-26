# The Amadio–Cardelli subtyping algorithm

Represent recursive types $\alpha, \beta$ by finite systems of equations $\varepsilon$ between type variables and type structures (their canonical forms), with root
variables $\alpha^*, \beta^*$. The algorithm derives judgments $\Sigma, \varepsilon \supset \alpha \le \beta$, where the *trail* $\Sigma$ is a finite set of assumptions $t \le s$ between
variables, by the rules

- $\Sigma, \varepsilon \supset t \le s$ if $t \le s \in \Sigma$; $\Sigma, \varepsilon \supset \bot \le \beta$; $\Sigma, \varepsilon \supset \alpha \le \top$; $\Sigma, \varepsilon \supset a \le a$ for a variable $a$ outside the domain of $\varepsilon$;
- $\Sigma, \varepsilon \supset \alpha \to \beta \le \alpha' \to \beta'$ if $\Sigma, \varepsilon \supset \alpha' \le \alpha$ and $\Sigma, \varepsilon \supset \beta \le \beta'$;
- $\Sigma, \varepsilon \supset t \le s$ if $\Sigma \cup \{t \le s\}, \varepsilon \supset \varepsilon(t) \le \varepsilon(s)$, for $t, s$ in the domain of $\varepsilon$.

Applied backwards from an initial goal, with the assumption rule taking priority, the rules generate an *execution tree*, which is always finite: its depth is
bounded by the product of the sizes of the two systems. Write $\alpha \le_A \beta$ if the execution tree for $\emptyset, \varepsilon_\alpha \cup \varepsilon_\beta \supset \alpha^* \le \beta^*$ succeeds.

The algorithm is [sound and complete](correctness-of-the-amadio-cardelli-subtyping-algorithm.md) for the [tree ordering](tree-ordering-on-recursive-types.md).

## Depends on

- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 4.1 (canonical forms and systems of equations), Section 4.2 (the rules, the initiality condition, execution trees, 4.2.2 termination and 4.2.3 the algorithm ordering).
