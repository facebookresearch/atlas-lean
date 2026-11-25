# Increasing failure rate implies new better than used

Let $T$ be a real random variable with $P(T > 0) = 1$, and let $S(t) = P(T > t)$ for $t \ge 0$. Say that $T$ has an increasing failure rate (IFR) if for every $x \ge 0$ the conditional survival probability $t \mapsto S(t + x)/S(t)$ is nonincreasing on $\{t \ge 0 : S(t) > 0\}$; this needs no density. Say that $T$ is new better than used (NBU) if $S(s + t) \le S(s)\,S(t)$ for all $s, t \ge 0$. Then every IFR lifetime is NBU.

Proof. If $S(s) = 0$, then $S(s + t) = 0$ and the inequality holds. Otherwise IFR with $x = t$, applied at the times $0 \le s$, gives $S(s + t)/S(s) \le S(t)/S(0) = S(t)$, since $S(0) = 1$. The exponential law, whose conditional survival probability does not depend on $t$, is both IFR and NBU with equality.

## Sources

- M. Hollander and F. Proschan, 'Nonparametric concepts and methods in reliability', in P. R. Krishnaiah and P. K. Sen (eds.), *Handbook of Statistics*, vol. 4, Elsevier, 1984, pp. 613-655, Definitions 2.4 and 2.7 and Figure 2.1
