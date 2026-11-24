# The elimination step preserves the unification specification

Let $x$ be a variable,
$t$ a term in which $x$ does not occur, $e$ an equation and $E$ a list of equations. Suppose
that for every substitution $s$, the two sides of $e$ become equal under $s$ exactly when
$s(x)$ equals the result of applying $s$ to $t$. Let $\sigma$ be the substitution that replaces
$x$ by $t$ and fixes every other variable, and let $E'$ be the list obtained by applying
$\sigma$ to both sides of every equation of $E$. Suppose an optional substitution $r$ satisfies
the unification specification for $E'$. Define the result $r'$ by: when $r$ returns a
substitution $s$, $r'$ returns $\sigma \gg s$, the composite that applies first $\sigma$ and
then $s$; when $r$ is failure, $r'$ is failure. Then $r'$ satisfies the unification
specification for the list with head $e$ and tail $E$.
