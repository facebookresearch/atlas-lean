# Costed insertion into a list

Let $a$ be an element of a linearly ordered type. Inserting
$a$ into the empty list returns $[a]$ at no cost. Inserting $a$ into a list with head $b$ and
tail $l$ first charges one unit for comparing $a \le b$; if $a \le b$ it returns $a$ followed by
$b$ and $l$, and otherwise it inserts $a$ into $l$, adding that cost, and returns $b$ followed by
the result.
