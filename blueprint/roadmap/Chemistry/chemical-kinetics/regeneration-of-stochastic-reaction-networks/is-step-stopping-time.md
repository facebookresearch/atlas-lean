# Stopping time of the step sequence

Let $S$ be a set, and consider step sequences $\omega = (\omega_n)_{n \in \mathbb{N}}$ with
$\omega_n = (\xi_n, E_n)$: a map $\xi_n : S \to S$ and a real clock value $E_n$. A function $\tau$
from step sequences to $\mathbb{N} \cup \{\infty\}$ is a stopping time of the step sequence if, for
every $n \in \mathbb{N}$ and all step sequences $\omega, \omega'$ with $\omega'_i = \omega_i$ for
every $i < n$,

$$\tau(\omega) = n \implies \tau(\omega') = n .$$

So whether $\tau(\omega) = n$ depends only on the first $n$ steps $\omega_0, \dots, \omega_{n-1}$;
for $n = 0$ the condition makes $\{\tau = 0\}$ either empty or the set of all step sequences.
Nothing is required at the value $\infty$, which stands for a time that never comes. The condition
is pointwise and involves no σ-algebra; measurability of $\tau$ is a separate property.
