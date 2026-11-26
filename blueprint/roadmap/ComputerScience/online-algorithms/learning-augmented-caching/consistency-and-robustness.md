# Consistency and robustness of learning-augmented online algorithms

A *learning-augmented online algorithm* receives, along with each input item, a prediction from an untrusted oracle, and its performance is measured against a prediction error $\eta \ge 0$ that vanishes on perfect predictions. The algorithm is *$\alpha$-consistent* if its competitive ratio is at most $\alpha$ whenever $\eta = 0$, *$\beta$-robust* if its competitive ratio is at most $\beta$ for all predictions, and *smooth* if its ratio degrades as a continuous function $f(\eta/\mathrm{OPT})$ between these extremes. The goal is to trade off $\alpha$ against $\beta$ while keeping $f$ graceful.

## Depends on

- [Deterministic online paging algorithm](../competitive-paging/deterministic-online-paging-algorithm.md)

## Sources

- Thodoris Lykouris, Sergei Vassilvitskii, "Competitive Caching with Machine Learned Advice", Journal of the ACM 68(4) (2021); ICML (2018), arXiv:1802.05399.
- Michael Mitzenmacher, Sergei Vassilvitskii, "Algorithms with Predictions", in Beyond the Worst-Case Analysis of Algorithms, Cambridge University Press (2021), arXiv:2006.09123.
- Manish Purohit, Zoya Svitkina, Ravi Kumar, "Improving Online Algorithms via ML Predictions", NeurIPS (2018).
