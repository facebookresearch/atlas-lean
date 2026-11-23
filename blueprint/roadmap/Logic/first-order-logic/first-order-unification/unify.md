# Martelli–Montanari unification

The algorithm takes a list of equations between terms and
returns a substitution or fails. On the empty list it returns the identity substitution.
Otherwise it looks at the first equation $t = u$ and the remaining list $E$. If $t$ and $u$ are
the same variable, or the same constant, the equation is dropped and the algorithm continues on
$E$; if they are two different constants, it fails. If $t$ is a variable $x$ and $u \ne x$, or
else $u$ is a variable $x$ and $t$ is not a variable, let $v$ be the other side: the algorithm
fails when $x$ occurs in $v$, and otherwise substitutes $v$ for $x$ on both sides of every
equation of $E$ and unifies the result; if that returns $s$, it returns the substitution that
applies first the replacement of $x$ by $v$ and then $s$, and if that fails, it fails. If $t$ and
$u$ are nodes with children $l_1, r_1$ and $l_2, r_2$, it continues on the list $l_1 = l_2$,
$r_1 = r_2$ followed by $E$. If one side is a constant and the other a node, it fails.
