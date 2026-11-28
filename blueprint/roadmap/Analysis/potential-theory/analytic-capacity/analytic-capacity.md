# Analytic capacity

For a set $K \subseteq \mathbb{C}$, typically compact, the analytic capacity $\gamma(K) \in [0, \infty]$ is the supremum of $|a|$ over all complex numbers $a$ for which there is a function $f : \mathbb{C} \to \mathbb{C}$ such that

- $f$ is complex differentiable on $\mathbb{C} \setminus K$;
- $|f(z)| \le 1$ for every $z \notin K$;
- $f(z) \to 0$ as $z \to \infty$;
- $z f(z) \to a$ as $z \to \infty$.

The limit $a$ is the derivative $f^\prime(\infty)$ of $f$ at infinity, so $\gamma(K) = \sup |f^\prime(\infty)|$ over these functions; the supremum of the empty set is $0$.
