# Sums over monotone Boolean functions by permutation classes

Let $n$ be a natural number and let $D_n$ be the set of monotone Boolean functions on $\{0,1\}^n$, for the coordinatewise order with $0 < 1$. For a Boolean function $b$ on $\{0,1\}^n$ and a permutation $\pi$ of the $n$ coordinates write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, where $(x \circ \pi)_i = x_{\pi(i)}$. Let $M$ be a commutative additive monoid and let $w$ assign an element of $M$ to every Boolean function on $\{0,1\}^n$, with $w(b^\pi) = w(b)$ for every Boolean function $b$ and every permutation $\pi$. Let $R \subseteq D_n$ be a finite set such that for every $f \in D_n$ there is exactly one $b \in R$ with $f = b^\pi$ for some permutation $\pi$, and let $\gamma(b)$ be the number of distinct functions $b^\pi$ as $\pi$ ranges over all permutations of the $n$ coordinates. Then

$$\sum_{f \in D_n} w(f) = \sum_{b \in R} \gamma(b)\, w(b),$$

where $\gamma(b)\, w(b)$ is the sum of $\gamma(b)$ copies of $w(b)$.
