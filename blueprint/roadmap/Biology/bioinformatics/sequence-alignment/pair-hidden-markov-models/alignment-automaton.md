# Weighted alignment automaton

A weighted alignment automaton with control states $Q$, alphabets $A$ and $B$ and weights in a set $R$ consists of

- a weight $w(q, c) \in R$ for reading the column $c$ in control state $q$;
- a next control state $\nu(q, c) \in Q$;
- a final weight $f(q) \in R$.
