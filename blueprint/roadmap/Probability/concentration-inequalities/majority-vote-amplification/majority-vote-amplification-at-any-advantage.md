# Majority-vote amplification at any advantage

Let $\Omega$ be a finite set, $G \subseteq \Omega$ with $|G| \ge (1 - \varepsilon)|\Omega|$ for some $0 \le \varepsilon < 1/2$, and $r \ge 1$. Then among all $2r$-tuples $(\omega_1, \dots, \omega_{2r}) \in \Omega^{2r}$, those with at most $r$ entries in $G$ form at most a

$$
\big(4\varepsilon(1-\varepsilon)\big)^{r}
$$

fraction. Equivalently, if $2r$ independent votes are each correct with probability at least $1 - \varepsilon$, the probability that they fail to have a strict correct majority is at most $(4\varepsilon(1-\varepsilon))^r$; for $\varepsilon = 1/3$ this is $(8/9)^r$.

## Proof sketch

For a fixed set $T$ of at least $r$ wrong positions out of $2r$, the probability that exactly the positions in $T$ are wrong is at most $\varepsilon^{|T|}(1-\varepsilon)^{2r - |T|} \le (\varepsilon(1-\varepsilon))^r$, since $\varepsilon \le 1 - \varepsilon$. There are at most $2^{2r} = 4^r$ such sets, giving $(4\varepsilon(1-\varepsilon))^r$.

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
