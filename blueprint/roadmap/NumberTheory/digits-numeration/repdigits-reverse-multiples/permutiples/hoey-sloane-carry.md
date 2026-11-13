# Carries of the Hoey–Sloane machine

Let $n$ and $b$ be natural numbers and let
$(d_0, \hat d_0)(d_1, \hat d_1) \cdots (d_k, \hat d_k)$ be an input string of pairs of natural
numbers. The carries $c_0, c_1, c_2, \dots$ of the $(n, b)$-Hoey–Sloane machine on this string
are the integers given by $c_0 = 0$,

$$c_{j+1} = \left\lfloor \frac{n \hat d_j - d_j + c_j}{b} \right\rfloor \quad (0 \le j \le k)$$

and $c_{j+1} = 0$ for $j > k$, where division by $b = 0$ gives $0$.

The machine has a transition from the state $c_j$ on the input $(d_j, \hat d_j)$ when this
division is exact.

## Sources

- B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025), Article A13, Section 4, Equation (2) (the Hoey-Sloane machine).
