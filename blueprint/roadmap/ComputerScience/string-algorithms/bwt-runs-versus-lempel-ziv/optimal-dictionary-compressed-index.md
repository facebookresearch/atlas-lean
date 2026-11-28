# Optimal-time attractor-bounded indexes

Given a string attractor of size $\gamma'$ for $T[1..n]$, there is an index of $O(\gamma'\max\{1, \log\frac{n}{\gamma'}\})$ words that finds all $\mathit{occ}$ occurrences of a pattern $P[1..m]$ in $O(m + (\mathit{occ} + 1)\log^{\varepsilon} n)$ time for any constant $\varepsilon > 0$, and with $O(\gamma'\max\{1, \log\frac{n}{\gamma'}\}\log^{\varepsilon} n)$ words in optimal $O(m + \mathit{occ})$ time. The logarithmic factor is saturated below by $1$: the set of all $n$ positions is an attractor, and an index that reports the occurrences of every single letter determines $T$, so for $\gamma' = n$ a binary $T$ needs $n$ bits, while the unsaturated bound $\gamma'\log(n/\gamma')$ would vanish.

## Proof sketch

Christiansen, Ettienne, Kociumaka, Navarro and Prezza build a run-length grammar of size $O(\gamma'\max\{1, \log(n/\gamma')\})$ whose nonterminals locally consistently parse the text (a recompression-style construction anchored at attractor positions), so that every occurrence of $P$ is found from a constant number of split points of the parse of $P$; primary occurrences are found by geometric range searching over the grammar's split points, and secondary occurrences are propagated through the grammar's parse tree in constant amortized time each.

## Depends on

- [String attractors](../string-attractors-and-repetitiveness-measures/string-attractor.md)

## Proof depends on

- [Universal compressed representations from string attractors](../string-attractors-and-repetitiveness-measures/attractor-universal-index.md)

## Sources

- Anders Roy Christiansen, Mikko Berggren Ettienne, Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Optimal-Time Dictionary-Compressed Indexes", ACM Transactions on Algorithms 17(1) (2021), arXiv:1811.12779.
