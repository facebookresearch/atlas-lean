# The word problem for Aut(Fₙ) is solvable in polynomial time

Let $n \ge 2$ and let $F_n$ be the
free group on $n$ generators. For every natural number $k$ and every family
$g_0, \dots, g_{k-1}$ of automorphisms of $F_n$ that generates $\operatorname{Aut}(F_n)$, the word
problem of $\operatorname{Aut}(F_n)$ for this family belongs to the complexity class P. Here a word
is a finite list of letters $(i, b)$ with $i \in \mathbb{N}$ and $b$ a boolean, the letter
$(i, \mathrm{true})$ standing for $g_i$ and $(i, \mathrm{false})$ for $g_i^{-1}$, and the word
problem is the decision problem on bitstrings that accepts exactly the bitstrings that decode,
under the canonical bitstring encoding of lists of pairs of a natural number and a boolean, to a
word whose letter indices are all below $k$ and whose product in $\operatorname{Aut}(F_n)$ is the
identity; bitstrings that do not decode to a word are rejected.

Schleimer proves (Theorem 5.2) that the word problem for $\operatorname{Aut}(F_m)$ is solvable in
polynomial time, and observes (Remark 5.1) that changing the generating set alters running times
by at most a multiplicative constant; the Kourovka Archive answers 16.109 "Yes, there is".

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.109 (V. E. Shpilrain); resolution: S. Schleimer, Polynomial-time word problems, Comment. Math. Helv. 83 (2008), 741-765, Theorem 5.2 (the word problem for Aut(F_m) is polynomial time) and Remark 5.1 (choosing a different generating set alters running times by at most a multiplicative constant); Kourovka Archive, Problem 16.109 (Yes, there is), https://wrap.warwick.ac.uk/44057/.
