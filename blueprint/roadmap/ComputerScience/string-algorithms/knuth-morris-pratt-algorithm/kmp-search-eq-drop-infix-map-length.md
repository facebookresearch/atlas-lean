# KMP search agrees with the first-infix split

Let $p$ and $t$ be lists over a type
with a lawful boolean equality, with $p$ nonempty. Let the first-infix split of $t$ by $p$ be
the pair $(u, v)$ with $t = u \, p \, v$ (concatenation) and $u$ as short as possible, or
nothing if $p$ does not occur in $t$. Then the value returned by KMP search for $p$ in $t$ is
the length of $u$ if the split exists, and no offset otherwise.
