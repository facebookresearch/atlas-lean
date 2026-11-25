# Costed insertion sort as a monadic insertion sort

Let $\beta$ be a linearly ordered type and $l$ a list over $\beta$. The generic monadic insertion
sort takes a comparison that returns a truth value inside a monad, and sorts by inserting the head
of the list into the recursively sorted tail, where inserting $a$ into a list with head $b$ runs
the comparison of $a$ with $b$ and places $a$ before $b$ when it returns true and otherwise
inserts $a$ further into the tail. Run in the time-counting monad with the charged comparison
(which returns the truth value of $x \le y$ and charges one unit), this generic sort coincides
with the costed insertion sort of $l$: the returned lists agree and the numbers of charged
comparisons agree.
