# Remainder bound from a second-derivative bound on a box

Let $n \in \mathbb{N}$, let $U \subseteq \mathbb{R}^n$ be open and contain the box
$[lo, hi] = \{y : lo_j \le y_j \le hi_j\}$, and let $i : \mathbb{R}^n \to \mathbb{R}$ be twice
continuously differentiable on $U$ with $\|D^2 i(y)\| \le M$ for every $y$ in the box (operator norm
for the sup norm $\|v\| = \max_j |v_j|$). If $v_0$ and $v_0 + dv$ lie in the box, the
[remainder](small-signal-remainder.md) $r = i(v_0 + dv) - i(v_0) - Di(v_0)[dv]$ satisfies
$|r| \le M \|dv\|^2 / 2$.
