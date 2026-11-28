# Learning-augmented weighted paging

Consider weighted paging with cache size $k$ in which every page weight is one of $\ell$ distinct values, so that pages fall into $\ell$ weight classes, and in which the request $\sigma_t$ at time $t$ comes with a prediction $\tau_t$ of the next time $\sigma_t$ is requested. With perfect predictions there is an $\ell$-competitive deterministic algorithm and an $O(\log \ell)$-competitive randomized algorithm, and both bounds are tight for $\ell \le k$; rounding weights in $[1, W]$ to powers of $2$ gives $O(\log W)$ and $O(\log \log W)$, compared with $k$ and $O(\log k)$ without predictions. For imperfect predictions, let $\epsilon$ be the weighted number of surprises: the sum over requests $s$ of the weight of $\sigma_s$, over those $s$ for which some request $t$ of the same weight class has $a_s < a_t$ but $\tau_s \ge \tau_t$, where $a_t$ is the true next request time. Then $\epsilon \le 2\eta$ for the weighted $\ell_1$ error $\eta = \sum_t w_{\sigma_t}|\tau_t - a_t|$, and there are algorithms with competitive ratios $O(\min\{\ell + \ell\epsilon/\mathrm{OPT},\, k\})$ (deterministic) and $O(\min\{\log \ell + \ell\epsilon/\mathrm{OPT},\, \log k\})$ (randomized).

## Proof sketch

Bansal, Coester, Kumar, Purohit and Vee split the cache among the weight classes and, inside each class, keep pages according to the predicted next-arrival order, as in Belady's farthest-in-future rule. The deterministic global strategy is a water-filling scheme in the style of Young's weighted-paging algorithm, evicting from each class at a rate inversely proportional to its weight, analyzed by a potential function built from the predicted requests; the randomized global strategy performs multiplicative updates on the class shares at rates read off from the structure of recent and predicted requests. With errors these give costs $\ell\,\mathrm{OPT} + 2\ell\epsilon$ and $O(\log \ell \cdot \mathrm{OPT} + \ell\epsilon)$, and combining them with the worst-case $k$- and $O(\log k)$-competitive weighted-paging algorithms gives the robust bounds. Tightness for perfect predictions is the lower bound of Jiang, Panigrahi and Sun and of Antoniadis, Coester, Eliáš, Polak and Simon.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)

## Proof depends on

- [Combining online algorithms for metrical task systems](combining-online-algorithms.md)

## Sources

- Nikhil Bansal, Christian Coester, Ravi Kumar, Manish Purohit, Erik Vee, "Learning-Augmented Weighted Paging", SODA (2022), arXiv:2011.09076, Section 1.1 and Theorems 1.1–1.4.
- Zhihao Jiang, Debmalya Panigrahi, Kevin Sun, "Online Algorithms for Weighted Paging with Predictions", ICALP (2020).
- Antonios Antoniadis, Christian Coester, Marek Eliáš, Adam Polak, Bertrand Simon, "Online Metric Algorithms with Untrusted Predictions", ICML (2020); ACM Transactions on Algorithms 19(2) (2023), arXiv:2003.02144.
