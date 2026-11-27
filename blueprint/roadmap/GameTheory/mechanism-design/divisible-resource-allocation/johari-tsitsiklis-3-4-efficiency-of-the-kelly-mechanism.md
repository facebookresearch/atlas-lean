# Johari–Tsitsiklis 3/4 efficiency of the Kelly mechanism

For admissible utilities with $U_i(0) \ge 0$, every Nash equilibrium of the price-anticipating Kelly game has aggregate utility at least $\frac34$ of the optimal aggregate utility. The bound is tight: for every $\varepsilon > 0$ some instance with linear utilities has a unique Nash equilibrium achieving less than $\frac34 + \varepsilon$ of the optimum.

## Proof sketch

Concavity reduces the worst case to linear utilities $U_i(x) = U_i'(d_i) x$ at the equilibrium; for linear utilities the ratio is a function of the equilibrium allocation whose minimum, computed explicitly, is $3/4$, approached with one large user and many small ones.

## Depends on

- [Kelly's proportional allocation mechanism](kellys-proportional-allocation-mechanism.md)

## Proof depends on

- [Existence and uniqueness of Kelly Nash equilibria and the modified potential](existence-and-uniqueness-of-kelly-nash-equilibria-and-the-modified-potential.md)

## Sources

- Ramesh Johari, "The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ramesh Johari and John N. Tsitsiklis, "Efficiency Loss in a Network Resource Allocation Game", Mathematics of Operations Research, 2004.
