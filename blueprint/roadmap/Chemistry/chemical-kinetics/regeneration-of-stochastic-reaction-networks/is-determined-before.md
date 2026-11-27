# Set of step sequences determined before a random time

Let $S$ be a set, consider step sequences $\omega = (\omega_n)_{n \in \mathbb{N}}$ with
$\omega_n = (\xi_n, E_n)$, $\xi_n : S \to S$ and $E_n \in \mathbb{R}$, and let $\tau$ be any
function from step sequences to $\mathbb{N} \cup \{\infty\}$. A set $C$ of step sequences is
determined before $\tau$ if, for every $n \in \mathbb{N}$, every $\omega \in C$ with
$\tau(\omega) = n$ and every step sequence $\omega'$ with $\omega'_i = \omega_i$ for all $i < n$,
also $\omega' \in C$. The sequence $\omega'$ need not satisfy $\tau(\omega') = n$, and nothing is
required of the sequences with $\tau(\omega) = \infty$.

When $\tau$ is a [stopping time of the step sequence](is-step-stopping-time.md), the condition says
exactly that, for every $n \in \mathbb{N}$, whether $\omega$ lies in $C \cap \{\tau = n\}$ depends
only on the first $n$ steps: the analogue, on $\{\tau < \infty\}$, of an event in the σ-algebra of
the past at $\tau$.
