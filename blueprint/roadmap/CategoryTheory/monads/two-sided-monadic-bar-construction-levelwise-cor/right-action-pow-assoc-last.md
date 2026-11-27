# Right Action Pow assoc last

Two successive iterated right actions equal the outermost/raw-last
multiplication `muAtPos (n+1) last` followed by `rightActionPow`. Proved by
induction via `rightActionPow_succ` and `muAtPos_succ_eq`; base case is the
right-module associativity.
