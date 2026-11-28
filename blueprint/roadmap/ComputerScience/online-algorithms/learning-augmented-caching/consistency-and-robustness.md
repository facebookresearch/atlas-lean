# Consistency and robustness of learning-augmented online algorithms

A *learning-augmented online algorithm* receives, along with each input item, a prediction from an untrusted oracle, and its performance is measured against a prediction error $\eta \ge 0$ that vanishes on perfect predictions. Following Purohit, Svitkina and Kumar, the algorithm is *$\alpha$-consistent* if its competitive ratio is at most $\alpha$ whenever $\eta = 0$, and *$\beta$-robust* if its competitive ratio is at most $\beta$ for all predictions; it is *smooth* if its ratio is bounded by a function $f(\eta/\mathrm{OPT})$ that degrades gracefully between these extremes. The goal is to trade off $\alpha$ against $\beta$ while keeping $f$ graceful. Lykouris and Vassilvitskii use a different vocabulary for the same desiderata: for the class of predictors with $\eta \le \epsilon \cdot \mathrm{OPT}$, an algorithm is $\beta$-consistent if its ratio is $\beta$ at $\epsilon = 0$, *$\alpha(\cdot)$-robust* if its ratio is $O(\alpha(\epsilon))$ (the rate of degradation), and *$\gamma$-competitive* if its ratio is at most $\gamma$ for every $\epsilon$ (the worst-case guarantee).

## Depends on

- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)

## Sources

- Thodoris Lykouris, Sergei Vassilvitskii, "Competitive Caching with Machine Learned Advice", Journal of the ACM 68(4) (2021); ICML (2018), arXiv:1802.05399, Definitions 2–6.
- Michael Mitzenmacher, Sergei Vassilvitskii, "Algorithms with Predictions", in Beyond the Worst-Case Analysis of Algorithms, Cambridge University Press (2021), arXiv:2006.09123.
- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
