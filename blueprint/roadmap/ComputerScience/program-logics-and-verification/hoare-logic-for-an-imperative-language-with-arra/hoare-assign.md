# Hoare rule for assignment in the imperative language with arrays

For every variable $x$, arithmetic expression $e$ and predicate $Q$ on states,

$$\lbrace s \mapsto Q(s[x \mapsto e(s)]) \rbrace\ x := e\ \lbrace Q \rbrace.$$
