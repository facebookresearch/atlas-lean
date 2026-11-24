# Fleming–Viot martingale-problem solutions satisfy the moment hierarchy

Let $E$ be a compact metric space and $B$ a bounded jump-type mutation operator on $C(E)$. For $n \ge 1$ and $f \in C(E^n)$ put $\Phi_f(\mu) = \langle f, \mu^{\otimes n} \rangle$, let $B^{(n)} = \sum_{i=1}^n B_i$ with $B_i$ acting in coordinate $i$, and for $i < j$ let $\Phi_{ij} : C(E^n) \to C(E^{n-1})$ identify coordinates $i$ and $j$. Suppose $X$ solves the Fleming–Viot martingale problem on $\mathcal M_1(E)$ for the generator

$$A \Phi_f = \Phi_{B^{(n)} f} + \sum_{1 \le i < j \le n} \bigl(\Phi_{\Phi_{ij} f} - \Phi_f\bigr)$$

on all such test functions. Since $A \Phi_f$ is bounded and continuous, the compensated processes are true martingales, and taking expectations shows that $m_n(t)(f) = \mathbb E \langle f, X_t^{\otimes n} \rangle$ satisfies the integral system of the [Fleming–Viot moment hierarchy](fleming-viot-moment-hierarchy-triangular-bounded.md),

$$m_n(t)(f) = m_n(0)(f) + \int_0^t \Bigl[m_n(s)(L_n f) + \sum_{i<j} m_{n-1}(s)(\Phi_{ij} f)\Bigr] ds, \qquad L_n = B^{(n)} - \tbinom n2 I,$$

with $m_n(0)(f) = \mathbb E \langle f, X_0^{\otimes n} \rangle$. For $n = 1$, $\mathbb E \langle f, X_t \rangle = \mathbb E \langle e^{tB} f, X_0 \rangle$.

## Depends on

- [Fleming-Viot moment hierarchy: triangular bounded Volterra system and unique solvability](fleming-viot-moment-hierarchy-triangular-bounded.md)
- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

A full proof page must still establish:

- the true-martingale property and the exchange of expectation and time integral;
- the case $n = 1$;
- for finite $E$ with parent-independent mutation, the reduction to the $K$-allele moment equations.

## Sources

- D. A. Dawson, "Measure-valued Markov processes", in *École d'Été de Probabilités de Saint-Flour XXI–1991*, Lecture Notes in Mathematics 1541, Springer, 1993, duality for Fleming–Viot, <https://link.springer.com/chapter/10.1007/BFb0084190>
