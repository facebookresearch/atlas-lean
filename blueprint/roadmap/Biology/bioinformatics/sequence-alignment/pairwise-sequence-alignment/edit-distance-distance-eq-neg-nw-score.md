# Unit-cost edit distance is a Needleman–Wunsch instance

For two sequences whose letters are compared for equality, the edit distance computed by the tabulated
dynamic program is minus the optimal global alignment score with substitution score $0$ for equal
letters and $-1$ otherwise, and gap score $-1$.
