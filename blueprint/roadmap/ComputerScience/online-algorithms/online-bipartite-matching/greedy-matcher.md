# Greedy as an online matcher

It replays the history to recover the left vertices it has
already matched (`greedyUsed`) and proposes the free neighbour of least index (`greedyPick`), the
choice of `Online.BipartiteMatching.step`.
