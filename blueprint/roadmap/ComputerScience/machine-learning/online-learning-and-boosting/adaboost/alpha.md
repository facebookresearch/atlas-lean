# AdaBoost's hypothesis weight

A weak hypothesis with weighted error
$\varepsilon \in \mathbb{R}$ gets the weight
$\alpha(\varepsilon) = \frac{1}{2} \log \frac{1 - \varepsilon}{\varepsilon}$, with the conventions $x / 0 = 0$, $\log 0 = 0$ and $\log x = \log \lvert x \rvert$ for $x < 0$; in particular $\alpha(0) = \alpha(1) = 0$. The usual interpretation of $\alpha$ as a log-odds weight assumes $0 < \varepsilon < 1$; the iteration does not
enforce it (a perfect weak hypothesis has $\varepsilon = 0$).
