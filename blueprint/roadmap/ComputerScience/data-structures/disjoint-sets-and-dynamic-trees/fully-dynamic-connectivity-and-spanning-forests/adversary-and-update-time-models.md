# Oblivious and adaptive adversaries; amortized and worst-case update time

Let $\mathcal{A}$ be a randomized dynamic algorithm processing an online sequence of updates $\sigma_1, \sigma_2, \dots$ and producing outputs (query answers, or a maintained object such as a spanning forest or a matching) after each step.

1. *Oblivious adversary*: the whole sequence $(\sigma_t)_t$ is fixed before $\mathcal{A}$ draws its random bits; guarantees are required for each fixed sequence.
2. *Adaptive adversary*: $\sigma_t$ may be any function of all outputs of $\mathcal{A}$ at steps $1, \dots, t-1$; guarantees must hold for all such strategies. Deterministic algorithms are automatically adaptive-robust.
3. *Worst-case* update time $u$: every single update takes time at most $u$. *Amortized* update time $u$: every prefix of $t$ updates takes total time at most $t \cdot u$. These quantify over operations, not over random bits: for a randomized algorithm each bound is further stated as *deterministic* (it holds for every outcome of the random bits), *expected* (the expected time of each update, respectively of each prefix, is at most $u$, respectively $t \cdot u$) or *w.h.p.* (it holds with probability at least $1 - n^{-c}$ for a constant $c$ of our choice).
4. *Las Vegas*: outputs are always correct and only the running time is random; *Monte Carlo*: running time is bounded and outputs are correct w.h.p.

## Depends on

- [Dynamic graph problems](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Amortized cost of an operation](../../amortized-analysis/amortized-cost.md)
- [Las Vegas and Monte Carlo algorithms](../../../randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)

## Sources

- Danupon Nanongkai, Thatchaphol Saranurak, "Dynamic Spanning Forest with Worst-Case Update Time: Adaptive, Las Vegas, and O(n^{1/2-epsilon})-Time", STOC (2017), arXiv:1611.03745.
- Shang-En Huang, Dawei Huang, Tsvi Kopelowitz, Seth Pettie, Mikkel Thorup, "Fully Dynamic Connectivity in O(log n (log log n)^2) Amortized Expected Time", TheoretiCS (2023), arXiv:1609.05867; full version of the extended abstracts by Thorup (STOC 2000) and by Huang, Huang, Kopelowitz and Pettie (SODA 2017).
