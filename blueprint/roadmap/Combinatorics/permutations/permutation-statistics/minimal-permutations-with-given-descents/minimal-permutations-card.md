# Minimal permutations of length two more than their number of descents

For every natural
number $d$, the number of permutations $\sigma$ of $\{0, 1, \dots, d + 1\}$ such that $\sigma$ has
exactly $d$ descents (positions $0 \le i \le d$ with $\sigma(i) > \sigma(i + 1)$) and, for every
position $j$, deleting the entry at position $j$ leaves a sequence of $d + 1$ entries with fewer
than $d$ descents, equals $2^{d+2} - (d + 1)(d + 2) - 2$.

## Sources

- Stefano Bilotta, Elisabetta Grazzini, and Elisa Pergola, "Enumeration of Two Particular Sets of Minimal Permutations", Journal of Integer Sequences 18 (2015), Article 15.10.2, Theorem `thm:enum`, lines 324-326, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Grazzini/graz3.tex>.
