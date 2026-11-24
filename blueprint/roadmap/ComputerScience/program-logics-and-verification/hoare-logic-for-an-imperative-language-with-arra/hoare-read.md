# Hoare rule for array reads in the imperative language with arrays

For every variable $x$, array $a$ of natural numbers, arithmetic expression $e$ and predicate $Q$ on states,

$$\lbrace s \mapsto e(s) < |a| \wedge Q(s[x \mapsto a_{e(s)}]) \rbrace\ x := a[e]\ \lbrace Q \rbrace,$$

where $|a|$ is the length of $a$: the precondition requires the index to be in bounds.
