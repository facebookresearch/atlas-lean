# Talagrand's numerical lemma

For $0 \le r \le 1$,

$$\inf_{0 \le \lambda \le 1} r^{-\lambda} e^{(1-\lambda)^2/4} \le 2 - r$$

(Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*, Publ.
Math. IHÉS 81 (1995), Lemma 4.1.3, taken there from Johnson and Schechtman). It is stated as the
existence of $\lambda \in [0, 1]$ with $e^{(1-\lambda)^2/4} \le (2 - r)\,r^{\lambda}$, and
$\lambda = 0$ unless $r > 0$. Talagrand takes $\lambda = 1 + 2\log r$ when $r \ge e^{-1/2}$ and
$\lambda = 0$ otherwise; the first case reduces to $e^{-a^2} \le 1 - (1 - e^{-a})^2$ for
$0 \le a \le 1/2$, which also follows from Taylor bounds for the exponential, without
Talagrand's study of a derivative.
