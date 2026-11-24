# Pitman's integral formula for merger rates when $2 \le k \le b$

Let $\Lambda$ be a finite measure on $[0, 1]$. For natural numbers $2 \le k \le b$, its [merger rate](merger-rate.md) is

$$\lambda_{b,k} = \int_{[0,1]} x^{k-2} (1 - x)^{b-k} \, \Lambda(dx).$$

The powers are natural-number powers with $0^0 = 1$. So an atom of $\Lambda$ at $0$ contributes
only to $\lambda_{b,2}$, where $x^{k-2} = x^0$, and an atom at $1$ only to $\lambda_{b,b}$, where
$(1 - x)^{b-k} = (1 - x)^0$. The integral is the mixed moment of $\Lambda$ of orders $k - 2$ and
$b - k$; since $2 \le k \le b$, neither difference is truncated at $0$.
