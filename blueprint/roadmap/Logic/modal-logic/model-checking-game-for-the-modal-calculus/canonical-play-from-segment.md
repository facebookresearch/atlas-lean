# Segments of canonical plays through fragment positions are bespoke plays

Let $M$ be a
Kripke model, $\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the
model-checking game on $M$. Write $\langle \psi, v \rangle$ for the game position with the
embedding of a fixpoint-free formula $\psi$, the world $v$ and the empty binder stack. Let $\pi$
be a play of the fragment game of $M$ and $\mathit{env}$ that conforms to the canonical
positional strategy induced by $\sigma$, and let $s, k \in \mathbb{N}$. Suppose every $\pi_i$
with $s \le i \le s + k$ is a fragment position $(\varphi_i, w_i)$, not $\mathrm{win}$ or
$\mathrm{lose}$. Then the list
$\langle \varphi_s, w_s \rangle, \langle \varphi_{s+1}, w_{s+1} \rangle, \dots,
\langle \varphi_{s+k}, w_{s+k} \rangle$ is a finite play from $\langle \varphi_s, w_s \rangle$
consistent with $\sigma$: each position has a game move to the next, and at Verifier-owned
positions the next position is the one $\sigma$ chooses.
