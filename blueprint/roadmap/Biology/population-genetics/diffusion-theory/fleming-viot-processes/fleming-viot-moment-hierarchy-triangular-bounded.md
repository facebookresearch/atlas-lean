# Fleming–Viot moment hierarchy: a triangular bounded Volterra system with unique solutions

Let $E$ be a compact metric space and $B$ a bounded jump-type mutation operator on $C(E)$, as given by a [bounded-rate jump Markov process](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/bounded-rate-jump-markov-process-on-a-compact-sp.md). For $n \ge 1$ let $B^{(n)} = \sum_{i=1}^n B_i$ on $C(E^n)$, with $B_i$ acting in coordinate $i$, a bounded operator; let $L_n = B^{(n)} - \binom n2 I$; and for $i < j$ let $\Phi_{ij} : C(E^n) \to C(E^{n-1})$ identify coordinates $i$ and $j$. Fix $T > 0$ and consider families of bounded, weak-* measurable maps $m_n : [0, T] \to C(E^n)^*$, $n \ge 1$, with $m_0 \equiv 1$, satisfying

$$m_n(t)(f) = m_n(0)(f) + \int_0^t \Bigl[m_n(s)(L_n f) + \sum_{1 \le i < j \le n} m_{n-1}(s)(\Phi_{ij} f)\Bigr] ds$$

for all $f \in C(E^n)$, $n \ge 1$ and $t \in [0, T]$. Such a family is uniquely determined by $(m_n(0))_{n \ge 1}$, by induction on $n$ and Gronwall's inequality in the dual norm, and is given by

$$m_n(t) = m_n(0) \circ e^{t L_n} + \int_0^t \sum_{i<j} m_{n-1}(s) \circ \Phi_{ij} \circ e^{(t-s) L_n}\, ds.$$

No commutation of the semigroup $e^{tB^{(n)}}$ with the diagonal maps $\Phi_{ij}$ is assumed or used: in general $e^{tB^{(2)}}$ does not commute with $\Phi_{12}$, for instance for two-state mutation, and the formula always applies $\Phi_{ij}$ after $e^{(t-s)L_n}$. For $n = 1$, $m_1(t) = m_1(0) \circ e^{tB}$.

## Depends on

- [Bounded-rate jump Markov process on a compact space by uniformization](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/bounded-rate-jump-markov-process-on-a-compact-sp.md)

## Proof depends on

- [Gronwall inequality (integral form)](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)
- [Duhamel's formula (variation of constants)](../../../../Analysis/ordinary-differential-equations/duhamel-variation-of-constants.md)

## Expansion

A full proof page must still establish:

- uniqueness by induction on $n$ and Gronwall's inequality in the dual norm, and the variation-of-constants formula;
- the case $n = 1$ and the non-commutation example.

Unbounded Feller mutation is a separate target, since it needs an approximation of the diagonal maps on the graph of the generator.

## Sources

- D. A. Dawson, "Measure-valued Markov processes", in *École d'Été de Probabilités de Saint-Flour XXI–1991*, Lecture Notes in Mathematics 1541, Springer, 1993, function-valued duality, <https://link.springer.com/chapter/10.1007/BFb0084190>
