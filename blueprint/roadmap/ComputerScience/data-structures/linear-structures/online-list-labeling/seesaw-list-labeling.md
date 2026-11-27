# Nearly optimal list labeling

For $m = (1 + \delta) n$ with $\delta \in (0, 1)$, the randomized *See-Saw* algorithm achieves amortized expected relabeling cost $O(\delta^{-1} \log n \, (\log\log n)^3)$ per insertion and deletion against an oblivious adversary; in the linear regime $m = (1 + \Theta(1)) n$ this is $O(\log n \, (\log\log n)^3)$. Since every randomized algorithm in this regime has amortized expected cost $\Omega(\log n)$ (Bulánek, Koucký and Saks), the bound is optimal up to a $(\log\log n)^3$ factor. It is achieved despite the lower bounds ruling out such costs for deterministic, smooth and history-independent algorithms, so the algorithm must be randomized, non-smooth and history dependent.

## Proof sketch

The See-Saw algorithm breaks the array into a recursive tree of subproblems whose siblings need not have equal sizes. Each subproblem draws a random rebuild window size and, at the end of every window of insertions, rebuilds its subtree, choosing how many slots to give each child from the insertions it has seen, a randomized prediction of which child will need more free slots. Dense subproblems and very small ones are leaves run with the classical algorithm, and the analysis bounds the total cost spent in dense leaves.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)
- [History-independent list labeling](history-independent-list-labeling.md)
- [Breaking the $\log^2 n$ barrier for list labeling](list-labeling-three-halves.md)
- [Tight lower bounds for deterministic list labeling](deterministic-list-labeling-lower-bound.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, Michal Koucký, William Kuszmaul, Michael Saks, "Nearly Optimal List Labeling", FOCS (2024), arXiv:2405.00807.
- Jan Bulánek, Michal Koucký, Michael Saks, "On Randomized Online Labeling with Polynomially Many Labels", ICALP (2013).
- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
