# Worst-case bounds for a mean with missing outcomes

Let $Y$ take values in a known interval $[a, b]$, let $R \in \{0, 1\}$ indicate whether $Y$ is observed, and let $q = P(R = 1)$. If $q > 0$, put $\mu_1 = E[Y \mid R = 1]$. Without assumptions on the missing outcomes, the set of values of $E[Y]$ compatible with the law of $(R, RY)$ is the interval $[q\mu_1 + (1-q)a,\ q\mu_1 + (1-q)b]$, and every point of it, endpoints included, is attained by setting $Y = t$ on $\{R = 0\}$ for a constant $t \in [a, b]$. If $q = 1$ the interval is the single point $\mu_1$. If $q = 0$, nothing about $Y$ is observed and the set is $[a, b]$.

## Sources

- Lecture slides, *5b. Partial Identification* (course ISS5096), Slide 2, 'No-Assumption Bounds', <https://j1yoo.github.io/assets/courses/eci/ECI_05b_Partial_Identification.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
