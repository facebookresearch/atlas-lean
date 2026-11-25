# The adversary's guess in the CPA experiment

Let $Y$ be an additive commutative group,
$f \colon X \to Y$ a function, $q$ a natural number, $\rho \colon \{0, \dots, q - 1\} \to X$ the
encryption randomness, $r_s \in X$ the challenge randomness and $b$ a bit. Let $c$ be an oracle
algorithm for the encryption oracle that outputs two messages $(m_0, m_1) \in Y \times Y$ and a
second-phase algorithm. The encryption query with index $i$, counting from $0$ across both
phases, is answered for a message $m$ by $(\rho_i, f(\rho_i) + m)$. Run $c$; when it outputs
$(m_0, m_1)$, run its second phase on the challenge ciphertext $(r_s, f(r_s) + m_b)$, where $m_b$
is $m_1$ if $b$ is true and $m_0$ otherwise. The guess is the output of the second phase. If the
two phases together ask more than $q$ encryption queries, the adversary is stopped and the guess
is false.
