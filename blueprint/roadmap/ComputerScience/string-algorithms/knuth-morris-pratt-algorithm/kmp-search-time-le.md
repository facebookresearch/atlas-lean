# KMP search makes linearly many comparisons

For any pattern $p$ and text $t$, lists over
a type with a boolean equality, KMP search for $p$ in $t$ makes at most $2|p| + 2|t|$ symbol
comparisons in total, those made while building the prefix table included, where $|p|$ and
$|t|$ are the lengths of $p$ and $t$.
