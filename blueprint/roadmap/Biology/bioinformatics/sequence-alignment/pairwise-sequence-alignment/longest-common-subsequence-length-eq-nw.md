# Longest common subsequence length is a Needleman–Wunsch instance

For a lawful `BEq`,
the length computed by the tabulated `longestCommonSubsequence` is the optimal global alignment
score with substitution score `if a == b then 1 else 0` and gap score `0`.
