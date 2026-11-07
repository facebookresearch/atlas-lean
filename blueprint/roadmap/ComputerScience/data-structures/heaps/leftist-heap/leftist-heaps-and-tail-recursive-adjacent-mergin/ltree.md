# Leftist invariant with correct stored ranks

Leftist invariant: stored rank is correct and left rank ≥ right rank
   For every node `N storedRank x l r`, require:
   - `storedRank = rank r + 1`;
   - `rank l ≥ rank r`;
   - `ltree l`;
   - `ltree r`.
