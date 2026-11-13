# Symmetric binary CSP

A binary constraint satisfaction problem is symmetric when, for
all variables $x, y$ and values $a, b$, the constraint on the ordered pair $(x, y)$ allows
$x = a$ together with $y = b$ exactly when the constraint on $(y, x)$ allows $y = b$ together
with $x = a$.

The condition concerns the allowed pairs for every ordered pair of variables; it does not
require the reverse of a listed arc to be listed.
