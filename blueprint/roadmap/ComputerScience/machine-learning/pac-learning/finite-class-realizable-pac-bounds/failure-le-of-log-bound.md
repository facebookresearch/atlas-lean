# Logarithmic sample size bounds the failure probability

Let $\alpha$ and $\beta$ be measurable spaces, $C$ a finite nonempty concept class of functions $\alpha \to \beta$ whose graphs $\{(x, y) : y = h(x)\}$ are measurable subsets of $\alpha \times \beta$ for every $h \in C$, and $A$ a learner from labeled samples of size $m$ that is consistent with $C$ (on every sample realizable by $C$, its output lies in $C$ and agrees with every observed label). Let $P$ be a probability measure on $\alpha$, $c \in C$ a measurable target, and $D_c$ the image of $P$ under $x \mapsto (x, c(x))$. The error of a hypothesis $h$ is $\mathrm{err}_{D_c}(h) = D_c\{(x, y) : h(x) \ne y\}$.

Let $\varepsilon, \delta \in (0, 1)$ and suppose the sample size satisfies

$$\frac{\log |C| + \log(1/\delta)}{\varepsilon} \le m .$$

Then

$$D_c^{\otimes m}\big\{S : \varepsilon < \mathrm{err}_{D_c}(A(S))\big\} \le \delta ,$$

where the left side is the outer measure of the failure event.
