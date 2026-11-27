# The square is operator convex

For self-adjoint elements $a, b$ of a star-ordered real
algebra and $0 \le t \le 1$, $(t a + (1 - t) b)^2 \le t a^2 + (1 - t) b^2$. This is the case $p = 2$ of the
operator convexity part of the Loewner–Heinz theorem (E. A. Carlen, *Trace inequalities and
quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 2.6), stated
for every star-ordered real algebra rather than only for matrices.

Here $t a + (1-t) b$ is again self-adjoint and the order is the star order ($x \le y$ when $y - x$ is a finite sum of elements $z^* z$, that is, lies in the additive closure of the set of such elements); for complex matrices this is the Loewner order, $A \le B$ when $B - A$ is positive semidefinite. The proof writes the gap as $t(1-t)(a-b)^2 = (s(a-b))^*(s(a-b))$ with $s = \sqrt{t(1-t)}$.

Operator convexity is much stronger than convexity of the trace functional $A \mapsto \operatorname{tr} A^2$: it asserts an inequality between operators, not between numbers.

## Informally uses

- [Convex-combination identity for squares](smul-sq-add-smul-sq-sub-sq.md): the proof rewrites the gap with this identity and recognises it as $z^* z$.

## Background

- [Klein's inequality for the square function](../../operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/klein-sq.md): a trace inequality for the same function $t \mapsto t^2$, the weaker, scalar kind of convexity statement that Carlen's notes contrast with operator convexity.

## Sources

- E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009 (published in *Entropy and the Quantum*, Contemp. Math. 529, 2010), Definition 2.1 and Theorem 2.6. Theorem numbers refer to that draft.
