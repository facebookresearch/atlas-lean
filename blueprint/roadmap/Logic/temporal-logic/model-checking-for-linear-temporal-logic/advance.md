# Computable fairness-counter update

The fairness counter update of the Büchi automaton of an LTL formula with $k$ fairness
requirements. For a counter $i < k$, entering the tableau state $t$ moves the counter to $i + 1$
if $t$ meets requirement $i$, and leaves it at $i$ otherwise; the value $k$, reached once every
requirement has been met in turn, is reset to $0$.
