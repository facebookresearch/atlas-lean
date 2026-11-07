# Gibonacci squares recurrence

Let $g : \mathbb{N} \to \mathbb{Z}$ satisfy
$g(n+2) = g(n+1) + g(n)$ for every $n \in \mathbb{N}$, and let $F_3 = 2$ be the third Fibonacci
number. Then for every $n \in \mathbb{N}$,

$$g(n+3)^2 = F_3\, g(n+2)^2 + F_3\, g(n+1)^2 - g(n)^2.$$

The characteristic polynomial $x^3 - 2x^2 - 2x + 1$ of this recurrence has roots $\alpha^2$,
$\beta^2$ and $-1$, where $\alpha$ and $\beta$ are the roots of $x^2 - x - 1$.

## Sources

- Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem 2 (label theorem02, equation equation02), lines 149–153, https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex
