# Complete rules for subtyping recursive types

Derive judgments $\Gamma \supset \alpha \le \beta$, where $\Gamma$ is a finite set of assumptions $t \le s$ between type variables, by:

- $\Gamma \supset \alpha \le \beta$ if $\alpha =_R \beta$ in the [complete equality rules](complete-rules-for-recursive-type-equality.md);
- transitivity; $\Gamma \supset t \le s$ for $t \le s \in \Gamma$; $\Gamma \supset \bot \le \alpha$; $\Gamma \supset \alpha \le \top$;
- $\Gamma \supset \alpha \to \beta \le \alpha' \to \beta'$ from $\Gamma \supset \alpha' \le \alpha$ and $\Gamma \supset \beta \le \beta'$;
- the Amber rule: $\Gamma \supset \mu t.\, \alpha \le \mu s.\, \beta$ from $\Gamma \cup \{t \le s\} \supset \alpha \le \beta$, where $t$ occurs only in $\alpha$, $s$ only in $\beta$, and neither occurs in $\Gamma$.

Write $\alpha \le_R \beta$ if $\emptyset \supset \alpha \le \beta$ is derivable. Then $\alpha \le_R \beta$ if and only if $\alpha \le_T \beta$ in the
[tree ordering](tree-ordering-on-recursive-types.md), if and only if the [subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md) succeeds on $\alpha \le \beta$.

## Depends on

- [Complete rules for equality of recursive types](complete-rules-for-recursive-type-equality.md)
- [The tree ordering on recursive types](tree-ordering-on-recursive-types.md)
- [The Amadio–Cardelli subtyping algorithm](the-amadio-cardelli-subtyping-algorithm.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 5.3 (the rules, including (µR) from the Amber language), Proposition 5.3.1 (soundness), Lemmas 5.4.1 and 5.4.3 (from execution trees to proof trees) and Theorem 5.4.5 (completeness).
