# Zuker exterior-loop recursion

With $V$ from [Zuker's recursion](zuker-vw.md), put $W(0) = 0$ and

$$W(n + 1) = \min\Bigl(W(n),\ \min_{0 \le i \le n} \bigl(W(i) + V(i, n + 1 - i)\bigr)\Bigr):$$

the last base of the prefix of length $n + 1$ is unpaired or closes an exterior branch $(i, n)$.
