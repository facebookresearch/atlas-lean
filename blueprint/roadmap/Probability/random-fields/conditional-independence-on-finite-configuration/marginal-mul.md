# Marginals of a product

Let $V$ and $\alpha$ be finite types, let $f$ and $g$ be real-valued
weights on the configurations $x : V \to \alpha$, and let $P, Q, U \subseteq V$ with
$P \cup Q = V$ and $P \cap Q \subseteq U$, such that $f(x)$ depends only on the values of $x$ on
$P$ and $g(x)$ only on its values on $Q$. Write $fg$ for the pointwise product, $P^c$ and $Q^c$
for the complements in $V$, and, for a weight $h$, a set $T \subseteq V$ and a configuration $x$,
$m_h(T, x)$ for the marginal of $h$ on $T$ at $x$, the total weight of the configurations that
agree with $x$ on $T$. Then for every configuration $x$,

$$m_{fg}(U, x) = m_f(U \cup P^c, x)\, m_g(U \cup Q^c, x).$$

Here the free variables of $f$ are those of $P$ outside $U$, and those of $g$ are those of $Q$
outside $U$.
