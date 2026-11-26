# Second fundamental theorem of asset pricing (finite one-period, gains form)

**Second fundamental theorem of asset pricing (finite one-period, gains form).** Let $\Omega$ be a finite nonempty set of states and $A$ a finite set of risky assets, and let $g_a(\omega) \in \mathbb{R}$ be the discounted gain of asset $a$ in state $\omega$. Assume there is no arbitrage: there is no portfolio $h : A \to \mathbb{R}$ with $\sum_a h_a g_a(\omega) \ge 0$ for all $\omega$ and $\sum_a h_a g_a(\omega) > 0$ for some $\omega$. Then the following are equivalent:

1. the market is complete: for every payoff $x : \Omega \to \mathbb{R}$ there are $c \in \mathbb{R}$ and $h : A \to \mathbb{R}$ with

$$x(\omega) = c + \sum_{a \in A} h_a g_a(\omega) \quad \text{for all } \omega \in \Omega;$$

2. there is exactly one $q : \Omega \to \mathbb{R}$ with $q(\omega) > 0$ for all $\omega$, $\sum_\omega q(\omega) = 1$ and $\sum_\omega q(\omega)\, g_a(\omega) = 0$ for every $a \in A$.

## Sources

- J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of continuous trading*, Stochastic Process. Appl. 11 (1981), 215–260; finite-market statement as in R. J. Williams, *Introduction to the Mathematics of Finance*, Amer. Math. Soc. (2006), Chapter 3 (second fundamental theorem of asset pricing).
