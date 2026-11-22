# Minimum value of the worst function

For $1 \le m \le n$ and every $L$,

$$
f_m(\bar x) = -\frac{L}{8} \cdot \frac{m}{m + 1} = \frac{L}{8}\Big(-1 + \frac{1}{m + 1}\Big),
$$

where $\bar x$ is the [minimiser](worst-minimizer.md): every difference $\bar x^{(i)} - \bar x^{(i+1)}$, $1 \le i \le m$ (with $\bar x^{(m+1)} = 0$), equals $1/(m+1)$. Together with [the minimum on the first $k$ coordinates](worst-function-ge-of-support.md) for $k = m$ and $L \ge 0$, this shows that $\bar x$ minimises $f_m$ and $f_m^* = \frac{L}{8}(-1 + \frac{1}{m+1})$, the value of the source.

## Informally uses

- [Minimiser of the worst function](worst-minimizer.md): the coordinates of $\bar x$.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.1.2: the value $f_k^*$.
