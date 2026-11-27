# Two utility representations differ by a strictly increasing map

Let $u, v : X \to \mathbb{R}$ both represent the same preference relation $\succsim$ on a set $X$, that is, $u(x) \ge u(y) \iff x \succsim y \iff v(x) \ge v(y)$ for all $x, y$. Then $f(u(x)) = v(x)$ well defines a function $f : u(X) \to \mathbb{R}$ on the set of attained values of $u$, $f$ is strictly increasing, and $v = f \circ u$. Proof: $u(x) = u(y)$ means $x \sim y$, so $v(x) = v(y)$; and $u(x) > u(y)$ means $x \succ y$, so $v(x) > v(y)$. Extending $f$ to a strictly increasing function on all of $\mathbb{R}$ needs further hypotheses and is not claimed; conversely, composing $u$ with any strictly increasing function gives another representation.

## Sources

- L. Blume, *Ordinal Representations*, lecture notes, Cornell University, §1, Definition 1 and remark, <https://www.cs.cornell.edu/courses/cs576/2006fa/576blumenotes1.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
