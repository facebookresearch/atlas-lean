# Sudakov minoration

There is a universal constant $L_1 > 0$ such that, for every centred Gaussian process of measurable random
variables on a probability space, indexed by a finite nonempty set $T$ whose points are pairwise $a$-separated for
the canonical distance, for some $a \ge 0$ ($d(s, t) \ge a$ whenever $s \ne t$),

$$\mathbb{E}\sup_{t \in T} X_t \ge \frac{a}{L_1}\sqrt{\log \operatorname{card} T}$$

(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, Lemma 2.10.2,
whose proof the book gives after Lemma 15.2.7). For independent standard Gaussians it is the
classical $\mathbb{E}\max_{k \le N} g_k \ge \sqrt{\log N}/L$ (Exercise 2.3.7), which the union
bound shows to be of the right order.
