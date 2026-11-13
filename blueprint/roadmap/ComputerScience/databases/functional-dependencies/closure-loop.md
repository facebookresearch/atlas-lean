# Iterated closure rounds

Let $F$ be a finite set of functional dependencies, $n$ a
natural number and $Y$ a finite set of attributes. The loop returns $Y$ if $n = 0$ or if one
closure round for $F$ leaves $Y$ unchanged; otherwise it returns the loop with $n - 1$ rounds
started from the result of one closure round applied to $Y$. Thus it repeats closure rounds from
$Y$ until nothing changes, for at most $n$ rounds.
