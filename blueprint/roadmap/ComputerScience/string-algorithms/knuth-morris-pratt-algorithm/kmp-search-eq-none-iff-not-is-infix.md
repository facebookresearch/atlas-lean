# KMP finds no match exactly when the pattern does not occur

For lists $p$ (the pattern)
and $t$ (the text) over a type with a lawful boolean equality, KMP search for $p$ in $t$ returns
no offset if and only if $p$ is not a contiguous sublist of $t$, that is, there are no lists
$u$, $v$ with $t = u \, p \, v$ (concatenation).
