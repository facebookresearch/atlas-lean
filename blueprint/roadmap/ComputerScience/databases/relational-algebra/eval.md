# Truth value of a selection condition

The truth value of a selection condition on a
tuple $t$ is defined by recursion: the always-true condition holds; $a = c$ holds when $t$ is
defined at $a$ with value $c$; $a = b$ holds when $t(a) = t(b)$ as possibly undefined values,
so it also holds when $t$ is undefined at both $a$ and $b$; a negation holds when the negated
condition fails; and a conjunction holds when both conditions hold.
