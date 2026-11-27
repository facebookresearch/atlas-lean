# Insertion sort with comparison cost

On a list over a linearly ordered type, insertion
sort returns the empty list at no cost when the input is empty. On a list with head $a$ and
tail $l$, it sorts $l$ and then inserts $a$ into the result by costed insertion; its cost is the
cost of sorting $l$ plus the cost of that insertion. Exactly one unit is charged for each order
comparison.
