# Failure probability of a consistent learner on a finite class

Let $\alpha$ and $\beta$ be measurable spaces, $C$ a finite concept class of functions $\alpha \to \beta$ whose graphs $\{(x, y) : y = h(x)\}$ are measurable subsets of $\alpha \times \beta$ for every $h \in C$, and $A$ a learner from labeled samples of size $m$ that is consistent with $C$ (on every sample realizable by $C$, its output lies in $C$ and agrees with every observed label). Let $P$ be a probability measure on $\alpha$, $c \in C$ a measurable target, and $D_c$ the image of $P$ under $x \mapsto (x, c(x))$. The error of a hypothesis $h$ is $\mathrm{err}_{D_c}(h) = D_c\{(x, y) : h(x) \ne y\}$.

For accuracy $\varepsilon \in (0, 1)$, the probability under $m$ i.i.d. samples from $D_c$ that the learner's output has error above $\varepsilon$ satisfies

$$D_c^{\otimes m}\big\{S : \varepsilon < \mathrm{err}_{D_c}(A(S))\big\} \le |C|\; e^{-\varepsilon m},$$

in $[0, \infty]$. The left side is the outer measure of the failure event; no measurability of the learner is assumed.
