# Satisfy-one with a variable fixed to false

Let $A$ be a proposition over
natural-number atoms and let $f$ be a natural number. If some assignment $\sigma$ with
$\sigma(f) = \mathrm{false}$ satisfies $A$, then the search for a satisfying path in the
restriction at $f := \mathrm{false}$ of the ROBDD of $A$ returns a path $p$, and the assignment
read off $p$ (the recorded value on each variable of $p$, false elsewhere), changed to send $f$
to $\mathrm{false}$, satisfies $A$.
