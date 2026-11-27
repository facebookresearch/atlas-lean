# Cbc Mac From

Let $X$ be an additive commutative group, $p : X \to X$ an arbitrary map (no invertibility is assumed), $a \in X$ a starting value and $m = (m_1, \dots, m_n)$ a message of $n$ blocks in $X$. The CBC-MAC chaining from $a$ folds $t \mapsto p(t + x)$ over the successive blocks:

$$
t_0 = a, \qquad t_i = p(t_{i-1} + m_i) \quad (1 \le i \le n),
$$

and returns $t_n$. On the empty message ($n = 0$) it returns the supplied starting value $a$.
