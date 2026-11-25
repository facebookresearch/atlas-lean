# The memoryless property characterizes the exponential law

Let $T$ be a real random variable with $T \ge 0$ almost surely, and let $S(t) = P(T > t)$ for $t \ge 0$. Then $T$ is memoryless, that is $S(s + t) = S(s)\,S(t)$ for all $s, t \ge 0$, if and only if either $T = 0$ almost surely or $T$ has the exponential law $\operatorname{Exp}(r)$ for some rate $r > 0$, so that $S(t) = e^{-rt}$.

Proof. Both laws are memoryless: $S \equiv 0$ for $T = 0$, and $S(t) = e^{-rt}$ for $\operatorname{Exp}(r)$. Conversely, $s = t = 0$ gives $S(0) = S(0)^2$, so $S(0) \in \{0, 1\}$, and $S(0) = 0$ means $T = 0$ almost surely. If $S(0) = 1$, right-continuity of $S$ gives $S > 0$ on some $[0, \varepsilon)$, and $S(t) = S(t/n)^n$ for every $n \ge 1$ gives $S(t) > 0$ for every $t \ge 0$. The function $g = -\log S$ is then finite, nondecreasing and additive on $[0, \infty)$, so $g(q) = q\,g(1)$ for every rational $q \ge 0$, and monotonicity extends this to $g(t) = rt$ for all $t \ge 0$ with $r = g(1) \ge 0$. Since $T$ is finite, $S(t) \to 0$ as $t \to \infty$, which excludes $r = 0$.

## Background

- [Mean of the exponential law](integral-id-exp-measure.md): the exponential law with rate $r$.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §2.4.3 (the memoryless property of the exponential distribution); the converse is derived above.
