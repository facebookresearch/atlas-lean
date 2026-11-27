# Agnostic PAC learning of a finite class

Let $h_1, \dots, h_M$ ($M \ge 1$) be classifiers $\alpha \to \{0,1\}$ whose error sets $\{(a, y) : h_j(a) \ne y\}$ are measurable. Let $m \ge 1$, $0 < \varepsilon < 1/2$ and $0 < \delta < 1$ with

$$m \ge \frac{\log(2M/\delta)}{2\varepsilon^2}.$$

Then empirical 0-1 risk minimization over the class is a PAC learner with $m$ examples, accuracy $2\varepsilon$ and confidence $\delta$ for the class $\{h_1, \dots, h_M\}$, over all data distributions on $\alpha \times \{0,1\}$; no realizability is assumed.
