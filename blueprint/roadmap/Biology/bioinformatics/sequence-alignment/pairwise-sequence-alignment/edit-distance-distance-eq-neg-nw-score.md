# Unit-cost edit distance is a Needleman–Wunsch instance

For a lawful `BEq`, the distance
computed by the tabulated `editDistance` is minus the optimal global alignment score with
substitution score `if a == b then 0 else -1` and gap score `-1`.
