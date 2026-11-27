# Continued-fraction Laplace transforms of birth–death transition probabilities

**Setting.** A general birth–death process (BDP) $X(t)$ on $\{0,1,2,\dots\}$ jumps from $n$ to $n+1$ at rate $\lambda_n$ and from $n$ to $n-1$ at rate $\mu_n$, with $\mu_0 = 0$. Its transition probabilities $P_{ab}(t) = \mathbb P(X(t) = b \mid X(0) = a)$ solve the Kolmogorov forward equations, which rarely have closed-form solutions for arbitrary rates. Let $f_{ab}(s) = \int_0^\infty e^{-st}P_{ab}(t)\,dt$. Define

$$a_1 = 1, \quad a_n = -\lambda_{n-2}\mu_{n-1}\ (n \ge 2), \qquad b_1 = s + \lambda_0, \quad b_n = s + \lambda_{n-1} + \mu_{n-1}\ (n \ge 2),$$

and let $B_n(s)$ be the denominators of the convergents of the continued fraction $\frac{a_1}{b_1+}\frac{a_2}{b_2+}\cdots$, given by $B_0 = 1$, $B_1 = b_1$ and $B_n = b_nB_{n-1} + a_nB_{n-2}$.

**Theorem.**

1. (Return to zero.)

$$f_{00}(s) = \cfrac{1}{s + \lambda_0 - \cfrac{\lambda_0\mu_1}{s + \lambda_1 + \mu_1 - \cfrac{\lambda_1\mu_2}{s + \lambda_2 + \mu_2 - \cdots}}} .$$

2. (General transitions.) For $b \le a$,

$$f_{ab}(s) = \Bigl(\prod_{j=b+1}^{a}\mu_j\Bigr)\,\cfrac{B_b(s)}{B_{a+1}(s) + \cfrac{B_a(s)\,a_{a+2}}{b_{a+2} + \cfrac{a_{a+3}}{b_{a+3} + \cdots}}},$$

and for $a \le b$,

$$f_{ab}(s) = \Bigl(\prod_{j=a}^{b-1}\lambda_j\Bigr)\,\cfrac{B_a(s)}{B_{b+1}(s) + \cfrac{B_b(s)\,a_{b+2}}{b_{b+2} + \cfrac{a_{b+3}}{b_{b+3} + \cdots}}}.$$

3. (First passage.) Making a set $S$ of states absorbing, by setting $\lambda_j = \mu_j = 0$ for $j \in S$, turns first-passage time distributions into transition probabilities of the modified process. For example, the density of the hitting time of $S$ from $i$ is the derivative of $\sum_{j\in S}P_{ij}(t)$, so the same continued fractions give Laplace transforms of first-passage times.

Truncating the continued fraction at a finite depth and inverting the Laplace transform numerically gives $P_{ab}(t)$ for arbitrary rates. These transition probabilities serve as likelihoods for discretely observed BDPs and as building blocks of EM algorithms and integral functionals.

## Expansion

Laplace-transforming the forward equations started from $0$ gives $sf_{00} - 1 = \mu_1f_{01} - \lambda_0f_{00}$ and $sf_{0b} = \lambda_{b-1}f_{0,b-1} + \mu_{b+1}f_{0,b+1} - (\lambda_b + \mu_b)f_{0b}$ for $b \ge 1$. Solving for the ratios $f_{0b}/f_{0,b-1}$ gives the recursion $\frac{f_{0b}}{f_{0,b-1}} = \frac{\lambda_{b-1}}{s + \lambda_b + \mu_b - \mu_{b+1}f_{0,b+1}/f_{0b}}$, and unrolling it yields the continued fraction for $f_{00}$. For general $(a,b)$, the same three-term recurrence links $f_{ab}$ across neighbouring $b$. The solution that is bounded as $b \to \infty$ is the minimal solution of this recurrence, which is expressed through the convergent denominators $B_n$ (Pincherle's theorem). This gives the products of rates times a tail continued fraction.

## Sources

- Forrest W. Crawford, Marc A. Suchard, "Birth-death processes", arXiv (2013). Section "Transition probabilities for general BDPs" (Laplace-transform recurrences, continued fraction for $f_{00}$, theorem for $f_{ab}$), subsection "First passage times". <https://doi.org/10.48550/arXiv.1301.1305>.
- Forrest W. Crawford, Marc A. Suchard, "Transition probabilities for general birth–death processes with applications in ecology, genetics, and evolution", Journal of Mathematical Biology 65(3) (2012), 553–580, <https://doi.org/10.1007/s00285-011-0471-z>: the refereed original of the Laplace-transform recurrences, the continued fraction for $f_{00}$ and the formula for $f_{ab}$ summarized in the review above.
