# Eliminating a solved variable lowers the number of variables

Let $x$ be a variable,
$t$ a term in which $x$ does not occur, and $E$ a list of equations. Applying the substitution
that replaces $x$ by $t$ (and fixes every other variable) to both sides of every equation of
$E$ gives a list of equations with strictly fewer distinct variables than the list obtained
by putting the equation $x = t$ in front of $E$.
