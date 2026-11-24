# Minimum of the worst function on the first $k$ coordinates

Let $n, m, k \in \mathbb{N}$ with $1 \le k \le m$, let $L \ge 0$, and let $f_m$ be the [worst
function](worst-function.md) on $\mathbb{R}^n$. If $z \in \mathbb{R}^n$ satisfies $z^{(j)} = 0$ for
every $j$ with $k < j \le \min(m, n)$, then

$$
f_m(z) \ge -\frac{L}{8} \cdot \frac{k}{k + 1} = \frac{L}{8}\Big(-1 + \frac{1}{k + 1}\Big).
$$

No relation between $m$ and $n$ is needed (the case of interest is $m \le n$). For $k = m$ the
hypothesis is empty, and the bound holds on all of $\mathbb{R}^n$. On such vectors
$f_m(z) = f_k(z) \ge f_k^*$, which is how the source argues (Corollary 2.1.1, with the value $f_k^*$
computed from $\bar x_k$). A direct proof drops the nonnegative terms beyond index $k$ and applies
the Cauchy–Schwarz inequality to the $k$ differences $d_i = z^{(i)} - z^{(i+1)}$, whose sum is
$z^{(1)}$: then $\sum d_i^2 \ge (z^{(1)})^2 / k$, and $\frac{1}{2} t^2 (1 + 1/k) - t \ge -\frac{k}{2(k+1)}$.

## Background

- [Minimum value of the worst function](worst-function-worst-minimizer.md): the bound is attained at $\bar x$ when $k = m \le n$.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.1.2: the value $f_k^* = \frac{L}{8}(-1 + \frac{1}{k+1})$ and Corollary 2.1.1.
