# Continuous-time Kaplan–Meier limit law with outer probability

Let $P$ be a product-integral map on $\ell^\infty([0, \tau])$, $P(A)(t) = \prod_{(0,t]}(1 + dA)$, given as a hypothesis together with Duhamel operators $\Psi$ on a domain $D$ satisfying the Duhamel equation, a uniform bound, the limit $\Psi(A, B)s \to \Psi(A, A)s$ as $B \to A$ within $D$ for $A \in D$ and $s$ in a class $S$ whose uniform closure contains $C[0, \tau]$, and the product formula on pure-jump integrators. For an arbitrary map $f$ into $[0, \infty]$, $E^*f$ denotes the outer integral (the infimum of $\int g$ over measurable $g \ge f$ almost everywhere) and $P^*$ the outer probability. Write $X_n \rightsquigarrow L$ for outer weak convergence: $E^*f(X_n) \to \int f\,dL$ for every bounded continuous $f \ge 0$. Let $\hat\Lambda_n$ and $\hat S_n$ be the Nelson–Aalen and Kaplan–Meier estimates of grouped censored samples with positive observation times, as elements of $\ell^\infty([0, \tau])$, and $S_\Lambda = P(-\Lambda)$ the survival function. If $\sqrt n(\hat\Lambda_n - \Lambda) \rightsquigarrow L$ with $L$ carried by $\{h : -h \in \overline S\}$, $-\Lambda \in D$ and $P^*(-\hat\Lambda_n \notin D) \to 0$, then $\sqrt n(\hat S_n - S_\Lambda)$ converges in the outer sense to the image of $L$ under $-\Psi(-\Lambda, -\Lambda)$.

## Sources

- A. W. van der Vaart and J. A. Wellner, "Weak Convergence and Empirical Processes", (1996), §1.2, Definition 1.3.3, Theorem 1.3.4, Theorem 1.11.1, Theorem 3.9.4.
- A. W. van der Vaart, "Asymptotic Statistics", (1998), Theorem 18.11, Theorem 20.8, §20.3.
- R. D. Gill and S. Johansen, "A survey of product-integration with a view toward application in survival analysis", Ann. Statist. 18 (1990), 1501–1555.
