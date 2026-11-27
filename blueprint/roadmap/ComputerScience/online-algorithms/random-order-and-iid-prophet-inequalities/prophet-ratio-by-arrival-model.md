# Gambler-to-prophet ratios under different arrival models

Let $X_1, \dots, X_n$ be independent nonnegative random variables with known distributions $F_1, \dots, F_n$. A gambler observes values one at a time and must irrevocably accept or reject each; a *stopping rule* $\tau$ receives $X_\tau$. For an arrival model $\mathcal{M}$, the *prophet ratio* is $\inf \mathbb{E}[X_\tau]/\mathbb{E}[\max_i X_i]$ over all instances, maximized over rules. The models are: *adversarial order* (a fixed known order); *i.i.d.* ($F_1 = \dots = F_n$); *random order* or *prophet secretary* (a uniformly random arrival order); and *order selection* (the gambler chooses the order in advance). A rule is *nonadaptive* if it fixes thresholds before any value is seen.

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk, Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research 46(4) (2021); EC (2017).
- Hossein Esfandiari, MohammadTaghi Hajiaghayi, Vahid Liaghat, Morteza Monemizadeh, "Prophet Secretary", SIAM Journal on Discrete Mathematics 31(3) (2017); ESA (2015).
- Bo Peng, Zhihao Gavin Tang, "Order Selection Prophet Inequality: From Threshold Optimization to Arrival Time Design", FOCS (2022); SIAM Journal on Computing, arXiv:2204.01425.
