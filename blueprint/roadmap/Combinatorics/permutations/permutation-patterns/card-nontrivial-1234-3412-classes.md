# Nontrivial classes under {1234, 3412}-pattern replacement

Let $n \ge 7$ and let $S_n$ be
the group of permutations of $\{0, 1, \dots, n - 1\}$. A move takes $\sigma \in S_n$ with positions
$i_1 < i_2 < i_3 < i_4$ such that $\sigma(i_1) < \sigma(i_2) < \sigma(i_3) < \sigma(i_4)$ to the
permutation $\tau$ with $\tau(i_1) = \sigma(i_3)$, $\tau(i_2) = \sigma(i_4)$,
$\tau(i_3) = \sigma(i_1)$, $\tau(i_4) = \sigma(i_2)$ and $\tau(j) = \sigma(j)$ for every other
position $j$; that is, it replaces an occurrence of the pattern $1234$ by one of $3412$. Call two
permutations equivalent when one is reached from the other by a finite sequence of moves and
reverse moves. Then the number of equivalence classes with more than one element is
$(n^3 + 6n^2 - 55n + 54)/6$.

This formula was conjectured by Ma; its values form sequence A330395 in the OEIS. The proof
decomposes the exceptional set into swap classes and a generic part. Kernel-checked finite
certificates handle the $S_5$ and $S_6$ classes, reachability in $S_7$ and the deletion boundary
in $S_8$. Point insertion then gives a recurrence, whose solution is the displayed polynomial.

## Sources

- Quinn Perian, Bella Xu, and Alexander Lu Zhang, "Counting the Nontrivial Equivalence Classes of Sn Under {1234,3412}-Pattern-Replacement", Journal of Integer Sequences 23 (2020), Article 20.10.2, Theorem `thm:nontrivial`, lines 172-175, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Zhang/zhang6.tex>.
