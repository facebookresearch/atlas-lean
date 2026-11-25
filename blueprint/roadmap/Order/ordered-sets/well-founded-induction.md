# Well-founded induction

If $R$ is a well-founded relation on a set $X$ and $A \subseteq X$ contains every $x \in X$ all of whose $R$-predecessors lie in $A$, then $A = X$. Mathlib states the equivalent form for properties of elements. Let $r$ be a well-founded relation on a type $X$ (classically, this means that every nonempty subset of $X$ has an $r$-minimal element), and let $P$ be a property of elements of $X$. Suppose that for every $x \in X$, if $P(y)$ holds for every $y$ with $y \mathrel{r} x$, then $P(x)$ holds. Then $P(a)$ holds for every $a \in X$. The relation need not be transitive or linear. Taking $P(x)$ to be the property $x \in A$ gives the familiar statement.

## Sources

- Jeremy Avigad, Leonardo de Moura, Soonho Kong and Sebastian Ullrich, Theorem Proving in Lean 4, §8.5, Well-Founded Recursion and Induction, https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/#well-founded-recursion-and-induction.
