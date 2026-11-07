# Global existence and uniqueness for globally Lipschitz ODEs

Let $E$ be a real Banach
space, let $f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be such that
$f(t, \cdot)$ is $L$-Lipschitz for every $t \in \mathbb{R}$. Then for every $t_0 \in \mathbb{R}$
and $x_0 \in E$ there is exactly one function $x : \mathbb{R} \to E$ with $x(t_0) = x_0$ and
$x'(t) = f(t, x(t))$ for every $t \in \mathbb{R}$.

Proof: local Picard--Lindelöf solutions are continued using the Gronwall bound of Teschl's
Theorem 2.17 and the extension criterion of Lemma 2.14.  Time reversal supplies the
negative-time solution, and global Gronwall uniqueness identifies every solution with the glued
one.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential equations`, entry `maximal solutions` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.2; stable ref https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem.
