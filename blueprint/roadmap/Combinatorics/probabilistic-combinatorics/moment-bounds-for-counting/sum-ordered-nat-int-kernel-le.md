# Shared-endpoint kernel bound with hypotheses on distinct pairs

Let $g$ and $P$ be natural numbers and let $c = (c_{ab})$ be a symmetric $g \times g$ matrix of
natural numbers, indexed by $\{0, \dots, g - 1\}$, whose off-diagonal row sums satisfy
$\sum_{b \ne a} c_{ab} \le P$ for every $a$. Call a pair $p = (p_1, p_2)$ of indices proper if
$p_1 \ne p_2$. Let $\kappa(p, q)$ be integers and $m \ge 0$ an integer such that, for all proper
pairs $p$ and $q$, $\kappa(p, q) \le m$, and $\kappa(p, q) = 0$ whenever $q$ shares no endpoint
with $p$ (that is, $q_1, q_2 \notin \{p_1, p_2\}$). Then

$$
\sum_{p \text{ proper}} \sum_{q \text{ proper}} c_{p_1 p_2} \, c_{q_1 q_2} \, \kappa(p, q) \le 4P \Bigl(\sum_{a} \sum_{b \ne a} c_{ab}\Bigr) m .
$$

The diagonal entries $c_{aa}$ and the values of $\kappa$ on pairs that are not proper are
arbitrary.
